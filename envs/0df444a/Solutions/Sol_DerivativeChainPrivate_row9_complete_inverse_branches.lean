-- Prove2me | solution 1 for DerivativeChainPrivate.row9_complete_inverse_branches
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T21:52:01.689891+00:00
-- url     : https://prove2.me/submissions/4c697094-502b-416f-8229-b37867542661

import Definitions.Def_DerivativeChainPrivate_fifth_row9_coefficient_bounds
import Definitions.Def_DerivativeChainPrivate_fifth_row9_inverse_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row9_newton_polynomials
import Definitions.Def_DerivativeChainPrivate_fifth_row9_residual
import Definitions.Def_DerivativeChainPrivate_fifth_row9_separation
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_row9_newton_inverse
import Theorems.Thm_DerivativeChainPrivate_row9_newton_residual
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


section
-- Source module: HermiteVerified

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Polynomial
namespace DerivativeChainPrivate.Hermite















end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite









end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite























end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite

lemma root_between (p : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ x ∈ Set.Ioo a b, p.eval x = 0 := by
  obtain ⟨x,hx,hroot⟩ := intermediate_value_Icc hab.le p.continuous.continuousOn
    (show (0:ℝ) ∈ Set.Icc (p.eval a) (p.eval b) from ⟨ha.le,hb.le⟩)
  refine ⟨x,⟨?_,?_⟩,hroot⟩
  · by_contra hn
    have he : x = a := by linarith [hx.1]
    subst x; linarith
  · by_contra hn
    have he : x = b := by linarith [hx.2]
    subst x; linarith









end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite













end DerivativeChainPrivate.Hermite
namespace DerivativeChainPrivate.Hermite





end DerivativeChainPrivate.Hermite

end


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
-- Source module: CubicRootCover

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cubic_three_roots_cover (g0 g1 g2 g3 a b c v : ℂ)
    (hg3 : g3 ≠ 0) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : g0+g1*a+g2*a^2+g3*a^3=0)
    (hb : g0+g1*b+g2*b^2+g3*b^3=0)
    (hc : g0+g1*c+g2*c^2+g3*c^3=0)
    (hv : g0+g1*v+g2*v^2+g3*v^3=0) : v=a ∨ v=b ∨ v=c := by
  have hB : g1+g2*(b+a)+g3*(b^2+b*a+a^2)=0 := by
    have hh : (b-a)*(g1+g2*(b+a)+g3*(b^2+b*a+a^2))=0 := by linear_combination hb-ha
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hab.symm)
  have hC : g1+g2*(c+a)+g3*(c^2+c*a+a^2)=0 := by
    have hh : (c-a)*(g1+g2*(c+a)+g3*(c^2+c*a+a^2))=0 := by linear_combination hc-ha
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hac.symm)
  have hsum : g2+g3*(a+b+c)=0 := by
    have hh : (b-c)*(g2+g3*(a+b+c))=0 := by linear_combination hB-hC
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hbc)
  have hf : g0+g1*v+g2*v^2+g3*v^3=g3*(v-a)*(v-b)*(v-c) := by
    linear_combination ha+(v-a)*hB+(v-a)*(v-b)*hsum
  rw [hf] at hv
  rcases mul_eq_zero.mp hv with h|h
  · rcases mul_eq_zero.mp h with h|h
    · have hh := (mul_eq_zero.mp h).resolve_left hg3
      exact Or.inl (sub_eq_zero.mp hh)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))
end DerivativeChainPrivate

end


section
-- Source module: NewtonSeparation

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem newton_branches_distinct (P₁ P₂ Y₁ Y₂ t : ℂ) (a b : ℝ)
    (ht : ‖t‖ ≤ 2) (hy₁ : ‖Y₁‖ ≤ 1/100000000000000) (hy₂ : ‖Y₂‖ ≤ 1/100000000000000)
    (hab : 1 < b-a) (happrox : ‖P₂-P₁-((b-a:ℝ):ℂ)‖ ≤ (9/10)*(b-a)) :
    P₁+t^32*Y₁ ≠ P₂+t^32*Y₂ := by
  have htail (Y : ℂ) (hy : ‖Y‖ ≤ 1/100000000000000) : ‖t^32*Y‖ ≤ 1/1000 := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ (2:ℝ)^32*(1/100000000000000) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ht 32) hy (norm_nonneg _) (by positivity)
      _ ≤ _ := by norm_num
  have h1 := htail Y₁ hy₁
  have h2 := htail Y₂ hy₂
  intro he
  have hid : ((b-a:ℝ):ℂ) = t^32*Y₁-t^32*Y₂-(P₂-P₁-((b-a:ℝ):ℂ)) := by linear_combination -he
  have hn : b-a ≤ ‖t^32*Y₁‖+‖t^32*Y₂‖+‖P₂-P₁-((b-a:ℝ):ℂ)‖ := by
    calc
      _ = ‖((b-a:ℝ):ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith only [hab])]
      _ = ‖t^32*Y₁-t^32*Y₂-(P₂-P₁-((b-a:ℝ):ℂ))‖ := congrArg norm hid
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  linarith only [hn,happrox,h1,h2,hab]
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
-- Source module: Row9AlphaRoots

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DerivativeChainPrivate
open Polynomial
theorem row9_alpha_exists_1 :
    ∃ α : ℝ, (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α ∧ α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ) ∧ α^3=(1001/2)+(-462)*α+(84)*α^2 := by
  let p : Polynomial ℝ := (X^3-C (84)*X^2-C (-462)*X-C (1001/2))
  obtain ⟨α,hα,hroot⟩ := Hermite.root_between p (show (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) < (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ) by norm_num)
    (by norm_num [p]) (by norm_num [p])
  refine ⟨α,hα.1.le,hα.2.le,?_⟩
  norm_num [p] at hroot
  linarith only [hroot]
theorem row9_alpha_exists_2 :
    ∃ α : ℝ, (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α ∧ α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ∧ α^3=(1001/2)+(-462)*α+(84)*α^2 := by
  let p : Polynomial ℝ := -(X^3-C (84)*X^2-C (-462)*X-C (1001/2))
  obtain ⟨α,hα,hroot⟩ := Hermite.root_between p (show (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) < (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) by norm_num)
    (by norm_num [p]) (by norm_num [p])
  refine ⟨α,hα.1.le,hα.2.le,?_⟩
  norm_num [p] at hroot
  linarith only [hroot]
theorem row9_alpha_exists_3 :
    ∃ α : ℝ, (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α ∧ α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ∧ α^3=(1001/2)+(-462)*α+(84)*α^2 := by
  let p : Polynomial ℝ := (X^3-C (84)*X^2-C (-462)*X-C (1001/2))
  obtain ⟨α,hα,hroot⟩ := Hermite.root_between p (show (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) < (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) by norm_num)
    (by norm_num [p]) (by norm_num [p])
  refine ⟨α,hα.1.le,hα.2.le,?_⟩
  norm_num [p] at hroot
  linarith only [hroot]
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
-- Source module: Row9BoundE1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_e_coefficient_bounds_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ)) :
    ∀ i : Fin 62, |row9ECoeffs α i| ≤ row9EBounds1 i := by
  have hm : |α-(115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9ECoeffs,row9EBounds1]
    apply (quadratic_midpoint_bound α (115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_e_norm_bound_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9E α t‖ ≤ 1/1000000000000000 := by
  apply (norm_real_power_sum_le (row9ECoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 62, row9EBounds1 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_e_coefficient_bounds_1 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9EBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundE2

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_e_coefficient_bounds_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) :
    ∀ i : Fin 62, |row9ECoeffs α i| ≤ row9EBounds2 i := by
  have hm : |α-(343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9ECoeffs,row9EBounds2]
    apply (quadratic_midpoint_bound α (343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_e_norm_bound_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9E α t‖ ≤ 1/1000000000000000 := by
  apply (norm_real_power_sum_le (row9ECoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 62, row9EBounds2 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_e_coefficient_bounds_2 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9EBounds2,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundE3

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_e_coefficient_bounds_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 62, |row9ECoeffs α i| ≤ row9EBounds3 i := by
  have hm : |α-(6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9ECoeffs,row9EBounds3]
    apply (quadratic_midpoint_bound α (6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_e_norm_bound_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9E α t‖ ≤ 1/1000000000000000 := by
  apply (norm_real_power_sum_le (row9ECoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 62, row9EBounds3 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_e_coefficient_bounds_3 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9EBounds3,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundJ1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_j_coefficient_bounds_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ)) :
    ∀ i : Fin 62, |row9JCoeffs α i| ≤ row9JBounds1 i := by
  have hm : |α-(115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9JCoeffs,row9JBounds1]
    apply (quadratic_midpoint_bound α (115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_j_norm_bound_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9J α t‖ ≤ 1/429496729600 := by
  apply (norm_real_power_sum_le (row9JCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 62, row9JBounds1 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_j_coefficient_bounds_1 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9JBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundJ2

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_j_coefficient_bounds_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) :
    ∀ i : Fin 62, |row9JCoeffs α i| ≤ row9JBounds2 i := by
  have hm : |α-(343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9JCoeffs,row9JBounds2]
    apply (quadratic_midpoint_bound α (343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_j_norm_bound_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9J α t‖ ≤ 1/429496729600 := by
  apply (norm_real_power_sum_le (row9JCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 62, row9JBounds2 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_j_coefficient_bounds_2 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9JBounds2,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundJ3

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_j_coefficient_bounds_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 62, |row9JCoeffs α i| ≤ row9JBounds3 i := by
  have hm : |α-(6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9JCoeffs,row9JBounds3]
    apply (quadratic_midpoint_bound α (6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_j_norm_bound_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9J α t‖ ≤ 1/429496729600 := by
  apply (norm_real_power_sum_le (row9JCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 62, row9JBounds3 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_j_coefficient_bounds_3 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9JBounds3,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundP1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_p_coefficient_bounds_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ)) :
    ∀ i : Fin 32, |row9PCoeffs α i| ≤ row9PBounds1 i := by
  have hm : |α-(115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9PCoeffs,row9PBounds1]
    apply (quadratic_midpoint_bound α (115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_p_norm_bound_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9P α t‖ ≤ 200 := by
  apply (norm_real_power_sum_le (row9PCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 32, row9PBounds1 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_p_coefficient_bounds_1 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9PBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundP2

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_p_coefficient_bounds_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) :
    ∀ i : Fin 32, |row9PCoeffs α i| ≤ row9PBounds2 i := by
  have hm : |α-(343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9PCoeffs,row9PBounds2]
    apply (quadratic_midpoint_bound α (343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_p_norm_bound_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9P α t‖ ≤ 200 := by
  apply (norm_real_power_sum_le (row9PCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 32, row9PBounds2 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_p_coefficient_bounds_2 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9PBounds2,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundP3

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_p_coefficient_bounds_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 32, |row9PCoeffs α i| ≤ row9PBounds3 i := by
  have hm : |α-(6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9PCoeffs,row9PBounds3]
    apply (quadratic_midpoint_bound α (6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_p_norm_bound_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9P α t‖ ≤ 200 := by
  apply (norm_real_power_sum_le (row9PCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 32, row9PBounds3 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_p_coefficient_bounds_3 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9PBounds3,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundQ1

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_q_coefficient_bounds_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ)) :
    ∀ i : Fin 32, |row9QCoeffs α i| ≤ row9QBounds1 i := by
  have hm : |α-(115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9QCoeffs,row9QBounds1]
    apply (quadratic_midpoint_bound α (115734900708924480683117605110581329654263378795671971321225058779403737867449466081667824420265361570345131911551887/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_q_norm_bound_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9Q α t‖ ≤ 1/10 := by
  apply (norm_real_power_sum_le (row9QCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 32, row9QBounds1 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_q_coefficient_bounds_1 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9QBounds1,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundQ2

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_q_coefficient_bounds_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) :
    ∀ i : Fin 32, |row9QCoeffs α i| ≤ row9QBounds2 i := by
  have hm : |α-(343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9QCoeffs,row9QBounds2]
    apply (quadratic_midpoint_bound α (343546891167944391458946282518786745242516542025683500135369487466919372785445095943539188721177926313290884236369239/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_q_norm_bound_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9Q α t‖ ≤ 1/10 := by
  apply (norm_real_power_sum_le (row9QCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 32, row9QBounds2 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_q_coefficient_bounds_2 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9QBounds2,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9BoundQ3

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_q_coefficient_bounds_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) :
    ∀ i : Fin 32, |row9QCoeffs α i| ≤ row9QBounds3 i := by
  have hm : |α-(6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632)| ≤ (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632:ℝ) := by
    rw [abs_le]
    constructor <;> linarith only [hlo,hhi]
  intro i
  fin_cases i
  all_goals
    dsimp [row9QCoeffs,row9QBounds3]
    apply (quadratic_midpoint_bound α (6160255249117403635520814849194759044356616276616839568758718745666958146958636820692389717679222539771877486223623961/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) (1/78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) _ _ _ hm).trans
    norm_num

theorem row9_q_norm_bound_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖row9Q α t‖ ≤ 1/10 := by
  apply (norm_real_power_sum_le (row9QCoeffs α) t 2 (by norm_num) ht).trans
  calc
    _ ≤ ∑ i : Fin 32, row9QBounds3 i * (2:ℝ)^i.val := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (row9_q_coefficient_bounds_3 α hlo hhi i) (by positivity)
    _ ≤ _ := by norm_num [row9QBounds3,Fin.sum_univ_succ]
end DerivativeChainPrivate

end


section
-- Source module: Row9Difference

set_option autoImplicit false
set_option maxHeartbeats 0
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_polynomial_difference (a b : ℝ) (t : ℂ) :
    row9P b t-row9P a t-((b-a:ℝ):ℂ) =
      ((b-a:ℝ):ℂ)*t*(∑ i : Fin 31, (row9DifferenceCoeffs (a+b) i:ℂ)*t^i.val) := by
  norm_num [row9P,row9PCoeffs,row9DifferenceCoeffs,Fin.sum_univ_succ]
  push_cast
  ring
end DerivativeChainPrivate

end


section
-- Source module: Row9Branch1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate

theorem row9_branch_exists_1 (α : ℝ)
    (hlo : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ))
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) :
    ∃ Y : ℂ → ℂ, DifferentiableOn ℂ Y (Metric.ball 0 2) ∧
      (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000 ∧
        row9G0 t+row9G1 t*(row9P α t+t^32*Y t)+row9G2 t*(row9P α t+t^32*Y t)^2+
          (-2)*(row9P α t+t^32*Y t)^3=0) ∧
      ∀ x : ℝ, |x| ≤ 2 → (Y (x:ℂ)).im=0 := by
  apply cubic_newton_branch row9G0 row9G1 row9G2 (row9P α) (row9Q α) (row9E α) (-2)
  · unfold row9G0; fun_prop
  · unfold row9G1; fun_prop
  · unfold row9G2; fun_prop
  · unfold row9P; fun_prop
  · unfold row9Q; fun_prop
  · unfold row9E; fun_prop
  · intro t
    simpa [row9G3] using row9_newton_residual α hα t
  · intro x
    simp [row9G0,row9G1,row9G2,row9P,row9Q,row9E,← Complex.ofReal_pow]
  · norm_num
  · norm_num
  · intro t ht
    refine ⟨row9_q_norm_bound_1 α hlo hhi t ht,row9_e_norm_bound_1 α hlo hhi t ht,?_,?_⟩
    · have hid := row9_newton_inverse α hα t
      simp only [row9G3,pow_zero,mul_one] at hid
      rw [hid,norm_mul,norm_pow]
      have hj := row9_j_norm_bound_1 α hlo hhi t ht
      calc
        _ ≤ (2:ℝ)^32*(1/(429496729600)) := by gcongr
        _ = _ := by norm_num
    · have hp := row9_p_norm_bound_1 α hlo hhi t ht
      have hg2 : ‖row9G2 t‖ ≤ 2640 := by
        have he : row9G2 t = (-42:ℂ)*t+168 := by dsimp [row9G2]; ring
        rw [he]
        calc
          _ ≤ ‖(-42:ℂ)*t‖+‖(168:ℂ)‖ := norm_add_le _ _
          _ ≤ 2640 := by norm_num [norm_mul]; linarith only [ht]
      calc
        _ ≤ ‖row9G2 t‖+‖3*(-2:ℂ)*row9P α t‖ := norm_add_le _ _
        _ ≤ 40000 := by norm_num [norm_mul]; linarith only [hg2,hp]
end DerivativeChainPrivate

end


section
-- Source module: Row9Branch2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate

theorem row9_branch_exists_2 (α : ℝ)
    (hlo : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ α) (hhi : α ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ))
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) :
    ∃ Y : ℂ → ℂ, DifferentiableOn ℂ Y (Metric.ball 0 2) ∧
      (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000 ∧
        row9G0 t+row9G1 t*(row9P α t+t^32*Y t)+row9G2 t*(row9P α t+t^32*Y t)^2+
          (-2)*(row9P α t+t^32*Y t)^3=0) ∧
      ∀ x : ℝ, |x| ≤ 2 → (Y (x:ℂ)).im=0 := by
  apply cubic_newton_branch row9G0 row9G1 row9G2 (row9P α) (row9Q α) (row9E α) (-2)
  · unfold row9G0; fun_prop
  · unfold row9G1; fun_prop
  · unfold row9G2; fun_prop
  · unfold row9P; fun_prop
  · unfold row9Q; fun_prop
  · unfold row9E; fun_prop
  · intro t
    simpa [row9G3] using row9_newton_residual α hα t
  · intro x
    simp [row9G0,row9G1,row9G2,row9P,row9Q,row9E,← Complex.ofReal_pow]
  · norm_num
  · norm_num
  · intro t ht
    refine ⟨row9_q_norm_bound_2 α hlo hhi t ht,row9_e_norm_bound_2 α hlo hhi t ht,?_,?_⟩
    · have hid := row9_newton_inverse α hα t
      simp only [row9G3,pow_zero,mul_one] at hid
      rw [hid,norm_mul,norm_pow]
      have hj := row9_j_norm_bound_2 α hlo hhi t ht
      calc
        _ ≤ (2:ℝ)^32*(1/(429496729600)) := by gcongr
        _ = _ := by norm_num
    · have hp := row9_p_norm_bound_2 α hlo hhi t ht
      have hg2 : ‖row9G2 t‖ ≤ 2640 := by
        have he : row9G2 t = (-42:ℂ)*t+168 := by dsimp [row9G2]; ring
        rw [he]
        calc
          _ ≤ ‖(-42:ℂ)*t‖+‖(168:ℂ)‖ := norm_add_le _ _
          _ ≤ 2640 := by norm_num [norm_mul]; linarith only [ht]
      calc
        _ ≤ ‖row9G2 t‖+‖3*(-2:ℂ)*row9P α t‖ := norm_add_le _ _
        _ ≤ 40000 := by norm_num [norm_mul]; linarith only [hg2,hp]
end DerivativeChainPrivate

end


section
-- Source module: Row9Branch3

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate

theorem row9_branch_exists_3 (α : ℝ)
    (hlo : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ α) (hhi : α ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ))
    (hα : α^3=(1001/2)+(-462)*α+(84)*α^2) :
    ∃ Y : ℂ → ℂ, DifferentiableOn ℂ Y (Metric.ball 0 2) ∧
      (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y t‖ ≤ 1/100000000000000 ∧
        row9G0 t+row9G1 t*(row9P α t+t^32*Y t)+row9G2 t*(row9P α t+t^32*Y t)^2+
          (-2)*(row9P α t+t^32*Y t)^3=0) ∧
      ∀ x : ℝ, |x| ≤ 2 → (Y (x:ℂ)).im=0 := by
  apply cubic_newton_branch row9G0 row9G1 row9G2 (row9P α) (row9Q α) (row9E α) (-2)
  · unfold row9G0; fun_prop
  · unfold row9G1; fun_prop
  · unfold row9G2; fun_prop
  · unfold row9P; fun_prop
  · unfold row9Q; fun_prop
  · unfold row9E; fun_prop
  · intro t
    simpa [row9G3] using row9_newton_residual α hα t
  · intro x
    simp [row9G0,row9G1,row9G2,row9P,row9Q,row9E,← Complex.ofReal_pow]
  · norm_num
  · norm_num
  · intro t ht
    refine ⟨row9_q_norm_bound_3 α hlo hhi t ht,row9_e_norm_bound_3 α hlo hhi t ht,?_,?_⟩
    · have hid := row9_newton_inverse α hα t
      simp only [row9G3,pow_zero,mul_one] at hid
      rw [hid,norm_mul,norm_pow]
      have hj := row9_j_norm_bound_3 α hlo hhi t ht
      calc
        _ ≤ (2:ℝ)^32*(1/(429496729600)) := by gcongr
        _ = _ := by norm_num
    · have hp := row9_p_norm_bound_3 α hlo hhi t ht
      have hg2 : ‖row9G2 t‖ ≤ 2640 := by
        have he : row9G2 t = (-42:ℂ)*t+168 := by dsimp [row9G2]; ring
        rw [he]
        calc
          _ ≤ ‖(-42:ℂ)*t‖+‖(168:ℂ)‖ := norm_add_le _ _
          _ ≤ 2640 := by norm_num [norm_mul]; linarith only [ht]
      calc
        _ ≤ ‖row9G2 t‖+‖3*(-2:ℂ)*row9P α t‖ := norm_add_le _ _
        _ ≤ 40000 := by norm_num [norm_mul]; linarith only [hg2,hp]
end DerivativeChainPrivate

end


section
-- Source module: Row9Separation12

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_difference_bound_12 (a b : ℝ)
    (hal : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a) (hau : a ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ))
    (hbl : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ b) (hbu : b ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) (t : ℂ) (ht : ‖t‖ ≤ 10/7) :
    1 < b-a ∧ ‖row9P b t-row9P a t-((b-a:ℝ):ℂ)‖ ≤ (9/10)*(b-a) := by
  have hgap : 1 < b-a := by linarith only [hau,hbl]
  refine ⟨hgap,?_⟩
  have hm : |a+b-(229640895938434436071031943814684037448389960410677735728297273123161555326447281012603506570721643941818008073960563/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816)| ≤ (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) := by rw [abs_le]; constructor <;> linarith only [hal,hau,hbl,hbu]
  have hcoeff : ∀ k : Fin 31, |row9DifferenceCoeffs (a+b) k| ≤ row9DifferenceBounds12 k := by
    intro k
    fin_cases k
    all_goals
      dsimp [row9DifferenceCoeffs,row9DifferenceBounds12]
      apply (quadratic_midpoint_bound (a+b) (229640895938434436071031943814684037448389960410677735728297273123161555326447281012603506570721643941818008073960563/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816) (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816) _ _ _ hm).trans
      norm_num
  rw [row9_polynomial_difference,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith only [hgap])]
  have hnorm := norm_real_power_sum_le (row9DifferenceCoeffs (a+b)) t (10/7) (by norm_num) ht
  have hsum : (∑ k : Fin 31, |row9DifferenceCoeffs (a+b) k| *(10/7:ℝ)^k.val) ≤
      ∑ k : Fin 31, row9DifferenceBounds12 k*(10/7:ℝ)^k.val := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hcoeff k) (by positivity)
  have hs : (10/7:ℝ)*(∑ k : Fin 31, row9DifferenceBounds12 k*(10/7:ℝ)^k.val) ≤ 9/10 := by
    norm_num [row9DifferenceBounds12,Fin.sum_univ_succ]
  calc
    _ ≤ (b-a)*(10/7)*(∑ k : Fin 31, row9DifferenceBounds12 k*(10/7:ℝ)^k.val) := by gcongr; exact hnorm.trans hsum
    _ ≤ (9/10)*(b-a) := by nlinarith only [mul_le_mul_of_nonneg_left hs (by linarith only [hgap] : 0 ≤ b-a)]
end DerivativeChainPrivate

end


section
-- Source module: Row9Separation13

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_difference_bound_13 (a b : ℝ)
    (hal : (57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a) (hau : a ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ))
    (hbl : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ b) (hbu : b ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) (t : ℂ) (ht : ‖t‖ ≤ 10/7) :
    1 < b-a ∧ ‖row9P b t-row9P a t-((b-a:ℝ):ℂ)‖ ≤ (9/10)*(b-a) := by
  have hgap : 1 < b-a := by linarith only [hau,hbl]
  refine ⟨hgap,?_⟩
  have hm : |a+b-(784498768728291014525491556788167546751359956926563942509992975555795235603260785846757192762435987667777827266896981/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704)| ≤ (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) := by rw [abs_le]; constructor <;> linarith only [hal,hau,hbl,hbu]
  have hcoeff : ∀ k : Fin 31, |row9DifferenceCoeffs (a+b) k| ≤ row9DifferenceBounds13 k := by
    intro k
    fin_cases k
    all_goals
      dsimp [row9DifferenceCoeffs,row9DifferenceBounds13]
      apply (quadratic_midpoint_bound (a+b) (784498768728291014525491556788167546751359956926563942509992975555795235603260785846757192762435987667777827266896981/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704) (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816) _ _ _ hm).trans
      norm_num
  rw [row9_polynomial_difference,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith only [hgap])]
  have hnorm := norm_real_power_sum_le (row9DifferenceCoeffs (a+b)) t (10/7) (by norm_num) ht
  have hsum : (∑ k : Fin 31, |row9DifferenceCoeffs (a+b) k| *(10/7:ℝ)^k.val) ≤
      ∑ k : Fin 31, row9DifferenceBounds13 k*(10/7:ℝ)^k.val := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hcoeff k) (by positivity)
  have hs : (10/7:ℝ)*(∑ k : Fin 31, row9DifferenceBounds13 k*(10/7:ℝ)^k.val) ≤ 9/10 := by
    norm_num [row9DifferenceBounds13,Fin.sum_univ_succ]
  calc
    _ ≤ (b-a)*(10/7)*(∑ k : Fin 31, row9DifferenceBounds13 k*(10/7:ℝ)^k.val) := by gcongr; exact hnorm.trans hsum
    _ ≤ (9/10)*(b-a) := by nlinarith only [mul_le_mul_of_nonneg_left hs (by linarith only [hgap] : 0 ≤ b-a)]
end DerivativeChainPrivate

end


section
-- Source module: Row9Separation23

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace DerivativeChainPrivate
open scoped BigOperators

theorem row9_difference_bound_23 (a b : ℝ)
    (hal : (171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a) (hau : a ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ))
    (hbl : (770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ b) (hbu : b ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) (t : ℂ) (ht : ‖t‖ ≤ 10/7) :
    1 < b-a ∧ ‖row9P b t-row9P a t-((b-a:ℝ):ℂ)‖ ≤ (9/10)*(b-a) := by
  have hgap : 1 < b-a := by linarith only [hau,hbl]
  refine ⟨hgap,?_⟩
  have hm : |a+b-(406487633767834251686235070732096611849945801165157691805880514570867344984005119789745556650025029130323023153749575/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352)| ≤ (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) := by rw [abs_le]; constructor <;> linarith only [hal,hau,hbl,hbu]
  have hcoeff : ∀ k : Fin 31, |row9DifferenceCoeffs (a+b) k| ≤ row9DifferenceBounds23 k := by
    intro k
    fin_cases k
    all_goals
      dsimp [row9DifferenceCoeffs,row9DifferenceBounds23]
      apply (quadratic_midpoint_bound (a+b) (406487633767834251686235070732096611849945801165157691805880514570867344984005119789745556650025029130323023153749575/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352) (1/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816) _ _ _ hm).trans
      norm_num
  rw [row9_polynomial_difference,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith only [hgap])]
  have hnorm := norm_real_power_sum_le (row9DifferenceCoeffs (a+b)) t (10/7) (by norm_num) ht
  have hsum : (∑ k : Fin 31, |row9DifferenceCoeffs (a+b) k| *(10/7:ℝ)^k.val) ≤
      ∑ k : Fin 31, row9DifferenceBounds23 k*(10/7:ℝ)^k.val := by
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_right (hcoeff k) (by positivity)
  have hs : (10/7:ℝ)*(∑ k : Fin 31, row9DifferenceBounds23 k*(10/7:ℝ)^k.val) ≤ 9/10 := by
    norm_num [row9DifferenceBounds23,Fin.sum_univ_succ]
  calc
    _ ≤ (b-a)*(10/7)*(∑ k : Fin 31, row9DifferenceBounds23 k*(10/7:ℝ)^k.val) := by gcongr; exact hnorm.trans hsum
    _ ≤ (9/10)*(b-a) := by nlinarith only [mul_le_mul_of_nonneg_left hs (by linarith only [hgap] : 0 ≤ b-a)]
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution :
    ∃ a1 a2 a3 : ℝ, ∃ Y1 Y2 Y3 : ℂ → ℂ,
      ((57867450354462240341558802555290664827131689397835985660612529389701868933724733040833912210132680785172565955775943/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a1 ∧ a1 ≤ (7233431294307780042694850319411333103391461174729498207576566173712733616715591630104239026266585098146570744471993/4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352:ℝ)) ∧ ((171773445583972195729473141259393372621258271012841750067684743733459686392722547971769594360588963156645442118184619/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ) ≤ a2 ∧ a2 ≤ (42943361395993048932368285314848343155314567753210437516921185933364921598180636992942398590147240789161360529546155/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ)) ∧ ((770031906139675454440101856149344880544577034577104946094839843208369768369829602586548714709902817471484685777952995/9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704:ℝ) ≤ a3 ∧ a3 ≤ (3080127624558701817760407424597379522178308138308419784379359372833479073479318410346194858839611269885938743111811981/39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816:ℝ)) ∧
      (DifferentiableOn ℂ Y1 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y1 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y1 (x:ℂ)).im=0)) ∧ (DifferentiableOn ℂ Y2 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y2 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y2 (x:ℂ)).im=0)) ∧ (DifferentiableOn ℂ Y3 (Metric.ball 0 2) ∧
        (∀ t : ℂ, ‖t‖ ≤ 2 → ‖Y3 t‖ ≤ 1/100000000000000) ∧
        (∀ x : ℝ, |x| ≤ 2 → (Y3 (x:ℂ)).im=0)) ∧
      ∀ t : ℂ, ‖t‖ ≤ 10/7 → ∀ v : ℂ,
        row9G0 t+row9G1 t*v+row9G2 t*v^2+(-2)*v^3=0 →
        v=(row9P a1 t+t^32*Y1 t) ∨ v=(row9P a2 t+t^32*Y2 t) ∨ v=(row9P a3 t+t^32*Y3 t) := by
  obtain ⟨a1,hal1,hau1,ha1⟩ := row9_alpha_exists_1
  obtain ⟨Y1,hol1,hstate1,hreal1⟩ := row9_branch_exists_1 a1 hal1 hau1 ha1
  obtain ⟨a2,hal2,hau2,ha2⟩ := row9_alpha_exists_2
  obtain ⟨Y2,hol2,hstate2,hreal2⟩ := row9_branch_exists_2 a2 hal2 hau2 ha2
  obtain ⟨a3,hal3,hau3,ha3⟩ := row9_alpha_exists_3
  obtain ⟨Y3,hol3,hstate3,hreal3⟩ := row9_branch_exists_3 a3 hal3 hau3 ha3
  refine ⟨a1,a2,a3,Y1,Y2,Y3,⟨hal1,hau1⟩,⟨hal2,hau2⟩,⟨hal3,hau3⟩,
⟨hol1,fun t ht => (hstate1 t ht).1,hreal1⟩,⟨hol2,fun t ht => (hstate2 t ht).1,hreal2⟩,⟨hol3,fun t ht => (hstate3 t ht).1,hreal3⟩,?_⟩
  intro t ht v hv
  have ht2 : ‖t‖ ≤ 2 := by linarith only [ht]
  obtain ⟨hgap12,happrox12⟩ := row9_difference_bound_12 a1 a2 hal1 hau1 hal2 hau2 t ht
  have hne12 : (row9P a1 t+t^32*Y1 t) ≠ (row9P a2 t+t^32*Y2 t) :=
    newton_branches_distinct _ _ _ _ t a1 a2 ht2 (hstate1 t ht2).1 (hstate2 t ht2).1 hgap12 happrox12
  obtain ⟨hgap13,happrox13⟩ := row9_difference_bound_13 a1 a3 hal1 hau1 hal3 hau3 t ht
  have hne13 : (row9P a1 t+t^32*Y1 t) ≠ (row9P a3 t+t^32*Y3 t) :=
    newton_branches_distinct _ _ _ _ t a1 a3 ht2 (hstate1 t ht2).1 (hstate3 t ht2).1 hgap13 happrox13
  obtain ⟨hgap23,happrox23⟩ := row9_difference_bound_23 a2 a3 hal2 hau2 hal3 hau3 t ht
  have hne23 : (row9P a2 t+t^32*Y2 t) ≠ (row9P a3 t+t^32*Y3 t) :=
    newton_branches_distinct _ _ _ _ t a2 a3 ht2 (hstate2 t ht2).1 (hstate3 t ht2).1 hgap23 happrox23
  exact cubic_three_roots_cover (row9G0 t) (row9G1 t) (row9G2 t) (-2)
    (row9P a1 t+t^32*Y1 t) (row9P a2 t+t^32*Y2 t) (row9P a3 t+t^32*Y3 t) v (by norm_num) hne12 hne13 hne23
    (hstate1 t ht2).2 (hstate2 t ht2).2 (hstate3 t ht2).2 hv
