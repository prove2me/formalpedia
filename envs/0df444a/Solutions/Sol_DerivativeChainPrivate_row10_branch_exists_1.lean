-- Prove2me | solution 1 for DerivativeChainPrivate.row10_branch_exists_1
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T22:26:18.736994+00:00
-- url     : https://prove2.me/submissions/d50cd975-d4bd-4dc4-83ce-154aafe94917

import Definitions.Def_DerivativeChainPrivate_fifth_row10_coefficient_bounds
import Definitions.Def_DerivativeChainPrivate_fifth_row10_inverse_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row10_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row10_residual
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row10_newton_inverse
import Theorems.Thm_DerivativeChainPrivate_row10_newton_residual
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


section
-- Source module: SepticSqrtAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators















theorem norm_real_power_sum_le {n : ℕ} (c : Fin n → ℝ) (u : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hu : ‖u‖ ≤ R) :
    ‖∑ i : Fin n, (c i:ℂ)*u^i.val‖ ≤ ∑ i : Fin n, |c i| *R^i.val := by
  calc
    _ ≤ ∑ i : Fin n, ‖(c i:ℂ)*u^i.val‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
      gcongr











end DerivativeChainPrivate

end


section
-- Source module: HolomorphicContraction


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology Set
open scoped NNReal
namespace DerivativeChainPrivate

theorem bounded_holomorphic_contraction (F : ℂ → ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hhol : Differentiable ℂ (fun p : ℂ × ℂ => F p.1 p.2))
    (hmap : ∀ t : ℂ, ‖t‖ ≤ R → ∀ v : ℂ, ‖v‖ ≤ M → ‖F t v‖ ≤ M)
    (hcontract : ∀ t : ℂ, ‖t‖ ≤ R → ∀ v w : ℂ, ‖v‖ ≤ M → ‖w‖ ≤ M →
      ‖F t v-F t w‖ ≤ (1/2)*‖v-w‖)
    (hreal : ∀ x y : ℝ, (F (x:ℂ) (y:ℂ)).im=0) :
    ∃ Y : ℂ → ℂ,
      (∀ t : ℂ, ‖t‖ ≤ R → ‖Y t‖ ≤ M ∧ F t (Y t)=Y t) ∧
      DifferentiableOn ℂ Y (Metric.ball 0 R) ∧
      ∀ x : ℝ, |x| ≤ R → (Y (x:ℂ)).im=0 := by
  classical
  have hex (t : ℂ) (ht : ‖t‖ ≤ R) : ∃ y : ℂ, ‖y‖ ≤ M ∧ F t y=y := by
    let S := Metric.closedBall (0:ℂ) M
    have hm : MapsTo (F t) S S := by
      intro v hv
      have hv' : ‖v‖ ≤ M := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hv
      simpa only [S,Metric.mem_closedBall,dist_zero_right] using hmap t ht v hv'
    have hc : ContractingWith (1/2:ℝ≥0) (hm.restrict (F t) S S) := by
      constructor
      · norm_num
      · apply LipschitzWith.of_dist_le_mul
        intro v w
        have hv : ‖(v:ℂ)‖ ≤ M := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using v.property
        have hw : ‖(w:ℂ)‖ ≤ M := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using w.property
        change dist (F t v) (F t w) ≤ ((1/2:ℝ≥0):ℝ)*dist (v:ℂ) (w:ℂ)
        simpa only [dist_eq_norm,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one] using hcontract t ht v w hv hw
    have hs : IsComplete S := Metric.isClosed_closedBall.isComplete
    have hz : (0:ℂ) ∈ S := by simpa only [S,Metric.mem_closedBall,dist_self] using hM
    obtain ⟨y,hy,hfy,_,_⟩ := ContractingWith.exists_fixedPoint' hs hm hc hz (edist_ne_top _ _)
    exact ⟨y,by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hy,hfy⟩
  let Y : ℂ → ℂ := fun t => if ht : ‖t‖ ≤ R then Classical.choose (hex t ht) else 0
  have hspec (t : ℂ) (ht : ‖t‖ ≤ R) : ‖Y t‖ ≤ M ∧ F t (Y t)=Y t := by
    dsimp only [Y]
    rw [dif_pos ht]
    exact Classical.choose_spec (hex t ht)
  have hiter_norm (t : ℂ) (ht : ‖t‖ ≤ R) (n : ℕ) : ‖((F t)^[n]) 0‖ ≤ M := by
    induction n with
    | zero => simpa using hM
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmap t ht _ ih
  have hiter_dist (t : ℂ) (ht : ‖t‖ ≤ R) (n : ℕ) :
      dist (((F t)^[n]) 0) (Y t) ≤ (1/2:ℝ)^n*M := by
    induction n with
    | zero => simpa only [Function.iterate_zero_apply,dist_zero_left,pow_zero,one_mul] using (hspec t ht).1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        _ = dist (F t (((F t)^[n]) 0)) (F t (Y t)) := by rw [(hspec t ht).2]
        _ ≤ (1/2)*dist (((F t)^[n]) 0) (Y t) := by
          simpa only [dist_eq_norm] using hcontract t ht _ _ (hiter_norm t ht n) (hspec t ht).1
        _ ≤ (1/2)*((1/2:ℝ)^n*M) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1/2:ℝ)^(n+1)*M := by rw [pow_succ]; ring
  have hiter_hol (n : ℕ) : Differentiable ℂ (fun t : ℂ => ((F t)^[n]) 0) := by
    induction n with
    | zero => simpa only [Function.iterate_zero_apply] using (differentiable_const (0:ℂ))
    | succ n ih =>
      have hh := hhol.comp (differentiable_id.prodMk ih)
      convert hh using 1 <;> first | rfl | simp only [Function.comp_def, Function.iterate_succ_apply', id_eq]
  have huniform : TendstoUniformlyOn (fun n : ℕ => fun t : ℂ => ((F t)^[n]) 0) Y atTop (Metric.closedBall 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hl : Tendsto (fun n : ℕ => (1/2:ℝ)^n*M) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_const M
    filter_upwards [hl.eventually (Iio_mem_nhds hε)] with n hn
    intro t ht
    have ht' : ‖t‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using ht
    simpa only [dist_comm] using lt_of_le_of_lt (hiter_dist t ht' n) hn
  refine ⟨Y,hspec,?_,?_⟩
  · exact (huniform.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall (fun n => (hiter_hol n).differentiableOn)) Metric.isOpen_ball
  · intro x hx
    have ht : (x:ℂ) ∈ Metric.closedBall (0:ℂ) R := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs] using hx
    have hr (n : ℕ) : (((F (x:ℂ))^[n]) 0).im=0 := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        have he : ((F (x:ℂ))^[n]) 0 = (((((F (x:ℂ))^[n]) 0).re:ℝ):ℂ) := by
          apply Complex.ext <;> simp [ih]
        rw [he]
        exact hreal x _
    have hlim := Complex.continuous_im.continuousAt.tendsto.comp (huniform.tendsto_at ht)
    exact tendsto_nhds_unique hlim (by simpa only [Function.comp_def,hr] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)))

#print axioms bounded_holomorphic_contraction
end DerivativeChainPrivate

end


section
-- Source module: QuadraticIntervalBound

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem quadratic_midpoint_bound (α m ε a b c : ℝ) (hα : |α-m| ≤ ε) :
    |a+b*α+c*α^2| ≤ |a+b*m+c*m^2|+ε*(|b+2*c*m|+|c| *ε) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hα
  have he : a+b*α+c*α^2 = (a+b*m+c*m^2)+(α-m)*(b+2*c*m)+c*(α-m)^2 := by ring
  rw [he]
  calc
    _ ≤ |a+b*m+c*m^2|+|(α-m)*(b+2*c*m)|+|c*(α-m)^2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |a+b*m+c*m^2|+ε*|b+2*c*m|+|c| *ε^2 := by
      simp only [abs_mul,abs_pow]
      gcongr
    _ = _ := by ring
end DerivativeChainPrivate

end


section
-- Source module: CubicNewtonBranch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate

 theorem cubic_newton_branch (g0 g1 g2 P Q E : ℂ → ℂ) (g3 : ℂ)
    (hg0 : Differentiable ℂ g0) (hg1 : Differentiable ℂ g1) (hg2 : Differentiable ℂ g2)
    (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q) (hE : Differentiable ℂ E)
    (hres : ∀ t, g0 t+g1 t*P t+g2 t*(P t)^2+g3*(P t)^3=t^32*E t)
    (hreal : ∀ x : ℝ, (g0 x).im=0 ∧ (g1 x).im=0 ∧ (g2 x).im=0 ∧
      (P x).im=0 ∧ (Q x).im=0 ∧ (E x).im=0)
    (hg3real : g3.im=0) (hg3 : ‖g3‖ ≤ 60)
    (hbound : ∀ t : ℂ, ‖t‖ ≤ 2 →
      ‖Q t‖ ≤ 1/10 ∧ ‖E t‖ ≤ 1/1000000000000000 ∧
      ‖1-Q t*(g1 t+2*g2 t*P t+3*g3*(P t)^2)‖ ≤ 1/100 ∧
      ‖g2 t+3*g3*P t‖ ≤ 40000) :
    ∃ Y : ℂ → ℂ,
      DifferentiableOn ℂ Y (Metric.ball 0 2) ∧
      (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000 ∧
        g0 t+g1 t*(P t+t^32*Y t)+g2 t*(P t+t^32*Y t)^2+g3*(P t+t^32*Y t)^3=0) ∧
      ∀ x : ℝ, |x| ≤ 2 → (Y (x:ℂ)).im=0 := by
  let H := fun t => 1-Q t*(g1 t+2*g2 t*P t+3*g3*(P t)^2)
  let A := fun t => Q t*t^32*(g2 t+3*g3*P t)
  let B := fun t => Q t*t^64*g3
  let F := fun t y => -Q t*E t+H t*y-A t*y^2-B t*y^3
  have hbounds (t : ℂ) (ht : ‖t‖ ≤ 2) :
      ‖-Q t*E t‖ ≤ 1/10000000000000000 ∧ ‖H t‖ ≤ 1/100 ∧
      ‖A t‖ ≤ 4000*2^32 ∧ ‖B t‖ ≤ 6*2^64 := by
    obtain ⟨hqt,het,hht,hat⟩ := hbound t ht
    refine ⟨?_,hht,?_,?_⟩
    · rw [norm_mul,norm_neg]
      calc
        _ ≤ (1/10:ℝ)*(1/1000000000000000) := mul_le_mul hqt het (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    · dsimp [A]
      rw [norm_mul,norm_mul,norm_pow]
      calc
        _ ≤ (1/10:ℝ)*2^32*40000 := by gcongr
        _ = _ := by ring
    · dsimp [B]
      rw [norm_mul,norm_mul,norm_pow]
      calc
        _ ≤ (1/10:ℝ)*2^64*60 := by gcongr
        _ = _ := by ring
  have hmap (t : ℂ) (ht : ‖t‖ ≤ 2) (v : ℂ) (hv : ‖v‖ ≤ 1/100000000000000) :
      ‖F t v‖ ≤ 1/100000000000000 := by
    obtain ⟨he,hh,ha,hb⟩ := hbounds t ht
    calc
      _ ≤ ‖-Q t*E t‖+‖H t*v‖+‖A t*v^2‖+‖B t*v^3‖ := by
        dsimp only [F]
        exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ 1/10000000000000000+(1/100:ℝ)*(1/100000000000000)+
          (4000*2^32)*(1/100000000000000)^2+(6*2^64)*(1/100000000000000)^3 := by
        simp only [norm_mul,norm_pow] at he ⊢
        gcongr
      _ ≤ _ := by norm_num
  have hcontract (t : ℂ) (ht : ‖t‖ ≤ 2) (v w : ℂ)
      (hv : ‖v‖ ≤ 1/100000000000000) (hw : ‖w‖ ≤ 1/100000000000000) :
      ‖F t v-F t w‖ ≤ (1/2)*‖v-w‖ := by
    obtain ⟨_,hh,ha,hb⟩ := hbounds t ht
    have hsum : ‖v+w‖ ≤ 2/100000000000000 := by
      have hn := norm_add_le v w
      linarith
    have hsum2 : ‖v^2+v*w+w^2‖ ≤ 3*(1/100000000000000:ℝ)^2 := by
      calc
        _ ≤ ‖v^2‖+‖v*w‖+‖w^2‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (1/100000000000000:ℝ)^2+(1/100000000000000)^2+(1/100000000000000)^2 := by
          simp only [norm_pow,norm_mul]
          gcongr
          rw [pow_two]
          exact mul_le_mul hv hw (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    have hid : F t v-F t w=(v-w)*(H t-A t*(v+w)-B t*(v^2+v*w+w^2)) := by dsimp [F]; ring
    rw [hid,norm_mul]
    have hn : ‖H t-A t*(v+w)-B t*(v^2+v*w+w^2)‖ ≤ 1/2 := by
      calc
        _ ≤ ‖H t‖+‖A t*(v+w)‖+‖B t*(v^2+v*w+w^2)‖ := (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ (1/100:ℝ)+(4000*2^32)*(2/100000000000000)+(6*2^64)*(3*(1/100000000000000)^2) := by
          simp only [norm_mul]
          gcongr
        _ ≤ _ := by norm_num
    nlinarith only [mul_le_mul_of_nonneg_left hn (norm_nonneg (v-w))]
  have hhol : Differentiable ℂ (fun p : ℂ × ℂ => F p.1 p.2) := by
    dsimp [F,H,A,B]
    fun_prop
  have hFr (x y : ℝ) : (F (x:ℂ) (y:ℂ)).im=0 := by
    obtain ⟨h0,h1,h2,hp,hq,he⟩ := hreal x
    dsimp [F,H,A,B]
    have hr (z : ℂ) (hz : z.im=0) : z=(z.re:ℂ) := by apply Complex.ext <;> simp [hz]
    rw [hr (Q x) hq,hr (E x) he,hr (g1 x) h1,hr (g2 x) h2,hr (P x) hp,hr g3 hg3real]
    simp [← Complex.ofReal_pow]
  obtain ⟨Y,hspec,hholY,hrealY⟩ := bounded_holomorphic_contraction F 2 (1/100000000000000)
    (by norm_num) (by norm_num) hhol hmap hcontract hFr
  refine ⟨Y,hholY,?_,hrealY⟩
  intro t ht
  obtain ⟨hy,hfix⟩ := hspec t ht
  refine ⟨hy,?_⟩
  have hqn : Q t ≠ 0 := by
    intro hzero
    have hh := (hbound t ht).2.2.1
    norm_num [hzero] at hh
  apply (mul_eq_zero.mp (show Q t*(g0 t+g1 t*(P t+t^32*Y t)+g2 t*(P t+t^32*Y t)^2+g3*(P t+t^32*Y t)^3)=0 from ?_)).resolve_left hqn
  dsimp [F,H,A,B] at hfix
  linear_combination Q t*(hres t)-t^32*hfix
end DerivativeChainPrivate

end


section
-- Source module: Row10BoundE1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_e_coefficient_bounds_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 62, |row10ECoeffs α i| ≤ row10EBounds1 i := by
  have hm : |α-(92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row10ECoeffs,row10EBounds1]
    apply (quadratic_midpoint_bound α (92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row10_e_norm_bound_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row10E α t‖ ≤ 1/1000000000000000 := by
  apply (norm_real_power_sum_le (row10ECoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 62, row10EBounds1 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row10_e_coefficient_bounds_1 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row10EBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row10BoundJ1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_j_coefficient_bounds_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 62, |row10JCoeffs α i| ≤ row10JBounds1 i := by
  have hm : |α-(92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row10JCoeffs,row10JBounds1]
    apply (quadratic_midpoint_bound α (92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row10_j_norm_bound_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row10J α t‖ ≤ 1/429496729600 := by
  apply (norm_real_power_sum_le (row10JCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 62, row10JBounds1 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row10_j_coefficient_bounds_1 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row10JBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row10BoundP1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_p_coefficient_bounds_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 32, |row10PCoeffs α i| ≤ row10PBounds1 i := by
  have hm : |α-(92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row10PCoeffs,row10PBounds1]
    apply (quadratic_midpoint_bound α (92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row10_p_norm_bound_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row10P α t‖ ≤ 200 := by
  apply (norm_real_power_sum_le (row10PCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 32, row10PBounds1 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row10_p_coefficient_bounds_1 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row10PBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row10BoundQ1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row10_q_coefficient_bounds_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 32, |row10QCoeffs α i| ≤ row10QBounds1 i := by
  have hm : |α-(92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row10QCoeffs,row10QBounds1]
    apply (quadratic_midpoint_bound α (92107901052725521193860113454723829693327250981942029050057129998946139476404642714736911071859726642925902220479445/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row10_q_norm_bound_1 (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row10Q α t‖ ≤ 1/10 := by
  apply (norm_real_power_sum_le (row10QCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 32, row10QBounds1 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row10_q_coefficient_bounds_1 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row10QBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (α : ℝ)
    (hlo : (23026975263181380298465028363680957423331812745485507262514282499736534869101160678684227767964931660731475555119861/19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408:ℝ) ≤ α) (hhi : α ≤ (46053950526362760596930056727361914846663625490971014525028564999473069738202321357368455535929863321462951110239723/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (hα : α^3=(1001/20)+(-66)*α+(21)*α^2) :
    ∃ Y : ℂ → ℂ, DifferentiableOn ℂ Y (Metric.ball 0 2) ∧
      (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000 ∧
        row10G0 t+row10G1 t*(row10P α t+t^32*Y t)+row10G2 t*(row10P α t+t^32*Y t)^2+
          (-60)*(row10P α t+t^32*Y t)^3=0) ∧
      ∀ x : ℝ, |x| ≤ 2 → (Y (x:ℂ)).im=0 := by
  apply cubic_newton_branch row10G0 row10G1 row10G2 (row10P α) (row10Q α) (row10E α) (-60)
  · unfold row10G0; fun_prop
  · unfold row10G1; fun_prop
  · unfold row10G2; fun_prop
  · unfold row10P; fun_prop
  · unfold row10Q; fun_prop
  · unfold row10E; fun_prop
  · intro t
    simpa [row10G3] using row10_newton_residual α hα t
  · intro x
    simp [row10G0,row10G1,row10G2,row10P,row10Q,row10E,← Complex.ofReal_pow]
  · norm_num
  · norm_num
  · intro t ht
    refine ⟨row10_q_norm_bound_1 α hlo hhi t ht,row10_e_norm_bound_1 α hlo hhi t ht,?_,?_⟩
    · have hid := row10_newton_inverse α hα t
      simp only [row10G3,pow_zero,mul_one] at hid
      rw [hid,norm_mul,norm_pow]
      have hj := row10_j_norm_bound_1 α hlo hhi t ht
      calc
        _ ≤ (2:ℝ)^32*(1/(429496729600)) := by gcongr
        _ = _ := by norm_num
    · have hp := row10_p_norm_bound_1 α hlo hhi t ht
      have hg2 : ‖row10G2 t‖ ≤ 2640 := by
        have he : row10G2 t = (1260:ℂ)+(-630:ℂ)*t+30*t^2 := by dsimp [row10G2]; ring
        rw [he]
        calc
          _ ≤ ‖(1260:ℂ)‖+‖(-630:ℂ)*t‖+‖(30:ℂ)*t^2‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
          _ ≤ 2640 := by norm_num [norm_mul,norm_pow]; nlinarith only [ht,norm_nonneg t]
      calc
        _ ≤ ‖row10G2 t‖+‖3*(-60:ℂ)*row10P α t‖ := norm_add_le _ _
        _ ≤ 40000 := by norm_num [norm_mul]; linarith only [hg2,hp]
