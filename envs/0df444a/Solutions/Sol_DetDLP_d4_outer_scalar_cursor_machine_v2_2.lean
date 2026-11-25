-- Prove2me | solution 2 for DetDLP.d4_outer_scalar_cursor_machine_v2
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T09:20:59.209339+00:00
-- url     : https://prove2.me/submissions/4c321d78-4568-40fe-86b4-0c04140da952

import Theorems.Thm_DetDLP_d4b_outer_caps_uniform
import Theorems.Thm_DetDLP_d4b_outer_branch_exact
import Theorems.Thm_DetDLP_d4b_outer_rate_absorption
import Theorems.Thm_DetDLP_d4b_outer_ranked_transcript
import Theorems.Thm_DetDLP_d4b_outer_step_poly
import Theorems.Thm_DetDLP_d4b_three_oracle_mux
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
import Definitions.Def_DetDLP_D4BEntryLengths
set_option autoImplicit false
namespace DetDLP.D4BBudget
open D4BEntry D4Plan Groundwork
noncomputable section
abbrev R {C c : ℕ} (x : Input C c) := (x.b:ℝ)/x.m+(x.b:ℝ)/Real.sqrt (logSafe x.m)
theorem rpos {C c : ℕ} (x : Input C c) : 0 ≤ R x := by positivity
def powR (k : ℕ) (r : ℝ) := (2:ℝ)^((k:ℝ)*r)
theorem pow1 (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ powR k r := Real.one_le_rpow (by norm_num) (mul_nonneg (by positivity) hr)
theorem powMono {a b : ℕ} {r : ℝ} (h : a ≤ b) (hr : 0 ≤ r) : powR a r ≤ powR b r := by unfold powR; apply Real.rpow_le_rpow_of_exponent_le (by norm_num); gcongr
theorem powAdd (a b : ℕ) (r : ℝ) : powR a r * powR b r = powR (a+b) r := by unfold powR; push_cast; rw [add_mul,Real.rpow_add (by norm_num : (0:ℝ)<2)]
theorem npK {i j : ℕ} (h : i≤j) (n : ℕ) : np i n ≤ np j n := Nat.mul_le_mul h (Nat.pow_le_pow_right (by omega) h)
theorem timeForm {C c : ℕ} (x : Input C c) (k : ℕ) : time x k = polyBound k (size x) * powR k (R x) := rfl
private def approx (F : ℕ → ℕ) (a : ℕ) (n : ℕ) (r : ℝ) := (F n:ℝ)*powR a r

theorem upgrade {F : ℕ → ℕ} (hF : PB F) (a : ℕ) : ∃ k : ℕ, ∀ n r, 0 ≤ r →
    approx F a n r ≤ polyBound k n*powR k r ∧ F n ≤ np k n := by
  obtain ⟨j,hj⟩ := hF; let k := max j a
  refine ⟨k,?_⟩; intro n r hr
  have h := (hj n).trans (npK (le_max_left j a) n)
  refine ⟨?_,h⟩; apply mul_le_mul _ (powMono (le_max_right j a) hr) (by unfold powR; positivity) (by unfold polyBound; positivity); rw [←np_cast]; exact_mod_cast h

theorem muxBudget (m k h : ℕ) : ∃ j : ℕ, ∀ n r, 0≤r →
    (m:ℝ)*(polyBound k n*powR k r + np h n + 1) ≤ polyBound j n*powR j r ∧
    (m:ℝ)*(polyBound k n + np h n + 1) ≤ polyBound j n := by
  let F (n : ℕ) := m*(np k n + np h n + 1)
  obtain ⟨j,H⟩ := upgrade (F:=F) ((PB.const m).mul (((np_pb k).add (np_pb h)).add (PB.const 1))) k
  refine ⟨j,?_⟩; intro n r hr; obtain ⟨t,s⟩ := H n r hr
  have one := pow1 k hr
  have hS : (F n:ℝ) ≤ polyBound j n := by rw [←np_cast]; exact_mod_cast s
  refine ⟨le_trans ?_ t,?_⟩
  · unfold approx F; push_cast; rw [np_cast k,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith only [mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (np h n)),one]
  · simpa only [F,Nat.cast_mul,Nat.cast_add,Nat.cast_one,np_cast] using hS

theorem scalarBudget (C e d k a : ℕ) : ∃ j : ℕ, ∀ n b l r p z, 0≤r → b ≤ 2*C*n → l ≤ np e n →
    p ≤ polyBound d n*powR d r → z ≤ (k*a:ℕ)*r →
    polyBound k (b+l)*p*(2:ℝ)^z ≤ polyBound j n*powR j r ∧ polyBound k (b+l) ≤ polyBound j n := by
  let base (n : ℕ) := np k (2*C*n+np e n)
  let F (n : ℕ) := base n*(np d n+1)
  have pb : PB base := (np_pb k).comp (((PB.const (2*C)).mul PB.id').add (np_pb e))
  obtain ⟨j,H⟩ := upgrade (F:=F) (pb.mul ((np_pb d).add (PB.const 1))) (d+k*a)
  refine ⟨j,?_⟩; intro n b l r p z hr hb hl hp hz; obtain ⟨t,s⟩ := H n r hr
  have he : (2:ℝ)^z ≤ powR (k*a) r := Real.rpow_le_rpow_of_exponent_le (by norm_num) hz
  have hb' : polyBound k (b+l) ≤ (base n:ℝ) := by rw [←np_cast]; exact_mod_cast np_mono k (Nat.add_le_add hb hl)
  have hb0 : 0 ≤ polyBound k (b+l) := by unfold polyBound; positivity
  have hz0 : 0 ≤ (2:ℝ)^z := by positivity
  have E : 0 ≤ powR d r := (zero_le_one.trans (pow1 d hr))
  have expand : approx F (d+k*a) n r = (base n:ℝ)*(((np d n:ℕ):ℝ)+1)* (powR d r * powR (k*a) r) := by simp [approx,F,powAdd]
  refine ⟨le_trans ?_ t,?_⟩
  · rw [expand]; calc
      _ ≤ ((base n:ℝ)*(polyBound d n*powR d r))*powR (k*a) r := mul_le_mul ((mul_le_mul_of_nonneg_left hp hb0).trans (mul_le_mul_of_nonneg_right hb' (mul_nonneg (by unfold polyBound; positivity) E))) he hz0 (by unfold polyBound powR; positivity)
      _ ≤ _ := by rw [np_cast d n]; nlinarith only [mul_nonneg (mul_nonneg (Nat.cast_nonneg (base n)) E) (zero_le_one.trans (pow1 (k*a) hr))]
  · apply hb'.trans; rw [←np_cast]; exact_mod_cast (Nat.le_mul_of_pos_right (base n) (Nat.succ_pos _)).trans s

theorem expPow {u r : ℝ} {a : ℕ} (hr : 0 ≤ r) (h : u ≤ a*r) : Real.exp u ≤ powR (2*a) r := by
  unfold powR; rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]; apply Real.exp_le_exp.mpr; push_cast
  nlinarith only [h,mul_le_mul_of_nonneg_right (show 1/2 ≤ Real.log 2 from by linarith [Real.log_two_gt_d9]) (mul_nonneg (Nat.cast_nonneg (α:=ℝ) a) hr)]

theorem roundsBudget (h a : ℕ) : ∃ j : ℕ, ∀ (n : ℕ) (r : ℝ) (N B W : ℕ), 0≤r → (N:ℝ) ≤ powR a r → (B:ℝ) ≤ powR a r+1 → W ≤ np h n →
    ((W+3+N*(B+1):ℕ):ℝ) ≤ polyBound j n*powR j r := by
  let F (n : ℕ) := np h n+8
  obtain ⟨j,H⟩ := upgrade (F:=F) ((np_pb h).add (PB.const 8)) (a+a)
  refine ⟨j,?_⟩; intro n r N B W hr hN hB hW; apply le_trans _ (H n r hr).1
  unfold approx F; push_cast; rw [←powAdd]; have E := pow1 a hr
  have HW : (W:ℝ) ≤ np h n := by exact_mod_cast hW
  have EN := zero_le_one.trans E
  have e2 := mul_le_mul_of_nonneg_right E EN
  have m := mul_le_mul hN (show (B:ℝ)+1 ≤ powR a r+1+1 by linarith) (by positivity) EN
  nlinarith only [HW,m,mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le E E) (Nat.cast_nonneg (α:=ℝ) (np h n)),e2,E]

theorem compilerBudget (L h t rK : ℕ) : ∃ j : ℕ, ∀ (n : ℕ) (r : ℝ) (rounds H : ℕ), 0≤r → H ≤ np h n → (rounds:ℝ) ≤ polyBound rK n*powR rK r →
    ((rounds:ℕ):ℝ)*(polyBound L H + L*(polyBound t n*powR t r+polyBound t n+1)) ≤ polyBound j n*powR j r ∧
    polyBound L H + L*(polyBound t n+1) ≤ polyBound j n := by
  let F (n : ℕ) := (np rK n+1)*(np L (np h n) + L*(2*np t n+1))
  have pb := ((np_pb rK).add (PB.const 1)).mul (((np_pb L).comp (np_pb h)).add ((PB.const L).mul (((PB.const 2).mul (np_pb t)).add (PB.const 1))))
  obtain ⟨j,Hj⟩ := upgrade (F:=F) pb (rK+t)
  refine ⟨j,?_⟩; intro n r rounds H hr hH hround; obtain ⟨ht,hs⟩ := Hj n r hr
  have E := pow1 t hr; have Er := pow1 rK hr
  have pL : polyBound L H ≤ (np L (np h n):ℝ) := by rw [←np_cast]; exact_mod_cast np_mono _ hH
  let D := np L (np h n) + L*(2*np t n+1)
  have t0 : 0 ≤ polyBound t n := by unfold polyBound; positivity
  have p : polyBound L H + L*(polyBound t n * powR t r + polyBound t n+1) ≤ (D:ℝ)*powR t r := by
    dsimp [D]; push_cast; rw [np_cast t]; have e' : polyBound t n*powR t r+polyBound t n+1 ≤ (2*polyBound t n+1)*powR t r := by nlinarith only [mul_le_mul_of_nonneg_left E t0,E]
    nlinarith only [mul_le_mul_of_nonneg_left e' (Nat.cast_nonneg (α:=ℝ) L),le_mul_of_one_le_right (Nat.cast_nonneg (α:=ℝ) (np L (np h n))) E,pL]
  refine ⟨le_trans ?_ ht,?_⟩
  · calc _ ≤ (polyBound rK n*powR rK r)*((D:ℝ)*powR t r) := mul_le_mul hround p (by unfold polyBound powR; positivity) (by unfold polyBound powR; positivity)
         _ ≤ _ := by unfold approx F; rw [←powAdd]; push_cast; dsimp [D]; push_cast; simp only [np_cast]; nlinarith only [mul_nonneg (mul_nonneg (by unfold polyBound; positivity : (0:ℝ)≤polyBound L (np h n)+L*(2*polyBound t n+1)) (zero_le_one.trans Er)) (zero_le_one.trans E)]
  · rw [←np_cast j n]; apply le_trans _ (by exact_mod_cast hs : (F n:ℝ) ≤ np j n); apply le_trans _ (by exact_mod_cast Nat.le_mul_of_pos_left D (Nat.succ_pos (np rK n)) : (D:ℝ) ≤ F n)
    dsimp [D]; push_cast; rw [np_cast t]; nlinarith only [pL,mul_nonneg (Nat.cast_nonneg (α:=ℝ) L) t0]
end
end DetDLP.D4BBudget

namespace DetDLP.D4BScalar
open D4Plan D4BOuter D4BEntry D4BBudget ResidualScalarOracle OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
abbrev Scalar :=
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ'),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            ∃ w : List Bool,
              EncodesTruncPoly P ℓ' w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
                (polyBound K (β + desc.length) * (Told : ℝ) *
                  (2 : ℝ) ^ ((K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ)))
                (polyBound K (β + desc.length))


set_option maxHeartbeats 900000 in
theorem obtainCalls (hscalar : Scalar) (C c e d : ℕ) (hc : 0<C) (D : PrimitiveMachine) (od : Fin D.tapeCount) :
    ∃ (M : PrimitiveMachine) (om : Fin M.tapeCount) (j : ℕ), ∀ {x : Input C c} (P : Plan x) {A o}, Enumerates A o e P → Digits D od d P →
      ∃ v : DigitsData P, (∀ u, unpack P.f x.l (qprec P) (P.R u) (h P u) (J P u) (v u) = BTNContract (P.R u) (P.V u)) ∧
      (∀ u a i, v u a i < 2^precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) ∧
      ∀ u a, RunsWithin M om (dgQuery P u a) (dgAns P v u a) (time x j) (polyBound j (size x)) := by
  let m := C+e+1; let l := d+e+1
  obtain ⟨M,om,k,hM⟩ := hscalar m l (Nat.succ_pos _) (Nat.succ_pos _) D od
  obtain ⟨a,ha⟩ := d4b_outer_rate_absorption C c hc
  obtain ⟨j,hj⟩ := scalarBudget C e d k a
  refine ⟨M,om,j,?_⟩; intro x P A o he hd
  let pp u := precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)
  let len u := spacing P.f (P.R u)*x.l
  let T u (z : Vect P u) := query P.f x.l (qprec P) P.hf (P.R u) (P.V u) (J P u) (h P u) (4*x.m*x.k) z
  obtain ⟨_,_,_,_,_,_,hlen,hp⟩ := he
  have hb := x.hb
  have bm : x.b ≤ 2*C*size x := by have hh := x.lower.trans (Nat.mul_le_mul_left C (m14a_separator_edge_budget x.spec).1); have := Nat.mul_le_mul_left (2*C) (Nat.le_add_right x.S x.desc.length); unfold size; nlinarith only [hh,this]
  have call (u : Fin P.N) (z : Vect P u) : ∃ w, EncodesTruncPoly (pp u) (len u) w (BTNContract (P.R u) (T u z)) ∧ RunsWithin M om (dgQuery P u z) w (time x j) (polyBound j (size x)) := by
    obtain ⟨t,ht,ht',ev⟩ := hd u z
    let dd := digitDesc P u z
    have hb1 : (1:ℝ) ≤ ((x.b+dd.length:ℕ):ℝ) := by exact_mod_cast (by omega : 1≤x.b+dd.length)
    have ev' : BTNEntryEvaluable dd (P.R u) (pp u) (len u) (T u z) D od t (((x.b+dd.length:ℕ):ℝ)^l) := by
      intro vi b; obtain ⟨w,h,tt,c,tr,stop,read,tm,sp⟩ := ev vi b
      exact ⟨w,h,tt,c,tr,stop,read,tm,fun i cf hi hcf => (sp i cf hi hcf).trans (pow_le_pow_right₀ hb1 (by dsimp [l]; omega))⟩
    have width : 1 ≤ h P u := le_max_left ..
    have nv : (P.R u).nV ≤ e*x.b := (Nat.le_mul_of_pos_right _ width).trans ((Nat.le_add_left _ _).trans (show (4*x.m*x.k)+(P.R u).nV*h P u ≤ pp u by unfold pp precision; omega)) |>.trans (hp u).1
    have coeff : e ≤ x.b^e := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hb _)
    have nv' : (P.R u).nV ≤ x.b^l := calc
      _ ≤ (x.b^e)*x.b := nv.trans (Nat.mul_le_mul_right _ coeff)
      _ ≤ x.b^l := by rw [←pow_succ]; apply Nat.pow_le_pow_right (by omega); dsimp [l]; omega
    have edge : (P.R u).nE ≤ m*x.b := (P.edges u) ▸ x.upper.trans (Nat.mul_le_mul_right _ (by dsimp [m]; omega))
    have me : e ≤ m := by dsimp [m]; omega
    have pp1 : 1 ≤ pp u := by unfold pp precision; omega
    have len1 : 1 ≤ len u := Nat.mul_pos (Nat.succ_pos _) x.hl
    obtain ⟨w,ok,tt,cf,tr,stop,read,tm,sp⟩ := hM x.b (pp u) (len u) t dd (P.R u) (T u z) hb ht edge nv' pp1 ((hp u).1.trans (Nat.mul_le_mul_right _ me)) len1 ((hp u).2.trans (Nat.mul_le_mul_right _ me)) ev'
    have ddle : dd.length ≤ np e (size x) := by exact_mod_cast (hlen u z).trans_eq (np_cast ..).symm
    have rho := (ha x).2 P u
    have exp' := mul_le_mul_of_nonneg_left rho (Nat.cast_nonneg (α:=ℝ) k)
    rw [mul_div_assoc',←mul_assoc,←Nat.cast_mul k a] at exp'
    have tt' : (t:ℝ) ≤ polyBound d (size x)*powR d (R x) := ht'.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (Nat.cast_nonneg d))) (by unfold polyBound; positivity))
    obtain ⟨tcap,scap⟩ := hj (size x) x.b dd.length (R x) t _ (rpos x) bm ddle tt' exp'
    exact ⟨w,ok,tt,cf,tr,stop,read,tm.trans tcap,fun i c hi hcf => (sp i c hi hcf).trans scap⟩
  choose W ok run using call
  have branch (u : Fin P.N) := DetDLP.d4b_outer_branch_exact P.f x.l (qprec P) P.hf (P.R u) (P.V u) (by have := x.hp; unfold qprec; omega) (h P u) (J P u) (4*x.m*x.k) ((Nat.lt_mul_div_succ _ (show 0 < h P u from lt_of_lt_of_le (by decide : 0<1) (le_max_left ..))).le) (P.edges u).le (W u) (ok u)
  choose v words caps exactValue using branch
  refine ⟨v,exactValue,caps,?_⟩; intro u a; unfold dgAns; rw [←words u a]; exact run u a

end DetDLP.D4BScalar

set_option autoImplicit false
namespace DetDLP.D4BFinish
open D4BEntry D4Plan D4BOuter D4BBudget DetDLP_W1_Queries MachineComposition Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
variable {C c : ℕ} {x : Input C c}
private theorem inputSpace {M o w y τ σ} (h : RunsWithin M o w y τ σ) : (w.length:ℝ) ≤ σ := by
  obtain ⟨t,f,_,_,_,_,hs⟩ := h
  apply le_trans _ (hs 0 _ (by omega) (.refl _)); exact_mod_cast (show w.length ≤ visitedSpace (locatedInit M w) by
    apply le_trans _ (Finset.single_le_sum (f:=(fun i => ((locatedInit M w).upper i-(locatedInit M w).lower i+1).toNat)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ M.inputTape)); simp [locatedInit]; omega)
private theorem listCap {α : Type} (f : α → List Bool) (xs : List α) (b : ℕ) (h : ∀ z ∈ xs, (f z).length ≤ b) :
    (Encoding.encodeList f xs).length ≤ (2*b+2)*xs.length+1 := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons x xs ih => have hh := h x (by simp); have ht := ih (fun y hy => h y (by simp [hy])); simp [Encoding.encodeList,flen,Nat.mul_succ]; omega
private theorem cnt (a q : ℕ) (h : a<2^q) : (countWord a).length ≤ q+1 := by
  by_cases hn : a=0; simp [hn,countWord]; rw [countWord,if_neg hn,Nat.size_eq_bits_len]; exact (Nat.size_le.mpr h).trans (by omega)
private theorem frameLen (a b : D4BOuter.Bits) : (pair a b).length = 2*a.length+1+b.length := by simp [pair,frame_correct,flen]
private theorem smallCap (C c s : ℕ) : ∃ k, ∀ (x : Input C c) {M o}, RunsWithin M o (input x) (answer x) (polyBound s (size x)) (polyBound s (size x)) →
    let st := listWord [countWord 0]; let H := np k (size x)
    (pair (input x) []).length ≤ H ∧ (pair st (tagWord 0 (input x))).length ≤ H ∧ (pair st (answer x)).length ≤ H ∧ (answer x).length ≤ H := by
  let F (n : ℕ) := 2*np s n+20+(2*(n+1)+2)*(2*C*n)+1
  have hF : PB F := ((((PB.const 2).mul (np_pb s)).add (PB.const 20)).add (((((PB.const 2).mul (PB.id'.add (PB.const 1))).add (PB.const 2))).mul ((PB.const (2*C)).mul PB.id'))).add (PB.const 1)
  obtain ⟨k,hk⟩ := hF; refine ⟨k,?_⟩; intro x M o h st H
  have i : (input x).length ≤ np s (size x) := by exact_mod_cast (inputSpace h).trans_eq (np_cast ..).symm
  have l : x.l ≤ 2*C*size x := by
    have hm := Nat.mul_le_mul_left (4*x.m) x.hk; have he := (m14a_separator_edge_budget x.spec).1
    have h' := Nat.mul_le_mul_left C (show x.m ≤ 2*x.S by omega); have hh := Nat.mul_le_mul_left (2*C) (Nat.le_add_right x.S x.desc.length); unfold D4Plan.size; nlinarith only [h',hh,x.lm]
  have ans : (answer x).length ≤ (2*(size x+1)+2)*(2*C*size x)+1 := by
    apply (listCap countWord _ (size x+1) ?_).trans (by simpa only [List.length_ofFn] using Nat.add_le_add_right (Nat.mul_le_mul_left _ l) 1)
    intro z hz; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz; exact (cnt _ x.p (ZMod.val_lt _)).trans (by have := x.pS; unfold D4Plan.size; omega)
  have hst : st.length = 5 := by decide
  have H0 : F (size x) ≤ H := hk _
  simp only [F] at H0; simp [frameLen,tagWord,hst]; omega

private theorem smallTrace (L H : ℕ) {O o τ σ} (hx : Nat.clog 2 x.S < L) (ini : (pair (input x) []).length ≤ H) (out : (answer x).length ≤ H)
    (h : Call O o τ σ H (listWord [countWord 0]) 0 (input x) (answer x)) : TraceAt L O o τ σ H (answer x) 2 (input x) [] := by
  right; refine ⟨listWord [countWord 0],tagWord 0 (input x),answer x,?_,ini,h.queryCap,out,h.run,?_⟩
  · change step L (pair (input x) []) = _; simp [step,nval,input,encodeTerminalBTNInstance,hx,tagWord]; rfl
  · left; refine ⟨?_,h.pairCap,out⟩; change step L (pair (listWord [countWord 0]) (answer x)) = _
    have hn : answer x ≠ [] := by unfold answer encodeNatListBin; cases List.ofFn (fun i : Fin x.l => ((Z x).coeff i.val : ZMod (2^x.p)).val) <;> simp [Encoding.encodeList]
    simp [step,nval,hn]

private theorem pbK {a b : ℕ} (h : a ≤ b) (n : ℕ) : polyBound a n ≤ polyBound b n := by rw [←np_cast,←np_cast]; exact_mod_cast npK h n
private theorem timeK {a b : ℕ} (h : a ≤ b) (x : Input C c) : time x a ≤ time x b := by
  apply mul_le_mul (pbK h _) (powMono h (rpos x)) (by unfold powR; positivity) (by unfold polyBound; positivity)
private theorem tagLen {st q : D4BOuter.Bits} {j H : ℕ} (hh : (pair st (tagWord j q)).length ≤ H) : q.length ≤ H := by
  rw [frameLen] at hh; unfold tagWord at hh; split at hh <;> simp only [List.length_cons] at hh <;> omega
private theorem tagMux (F A D : PrimitiveMachine) (of₀ : Fin F.tapeCount) (oa : Fin A.tapeCount) (od : Fin D.tapeCount) : ∃ (O : PrimitiveMachine) (k : ℕ),
    (∀ w y τ σ, RunsWithin F of₀ w y τ σ → RunsWithin O O.inputTape (tagWord 0 w) y (k*(τ+w.length+1)) (k*(σ+w.length+1))) ∧
    (∀ w y τ σ, RunsWithin A oa w y τ σ → RunsWithin O O.inputTape (tagWord 1 w) y (k*(τ+w.length+1)) (k*(σ+w.length+1))) ∧
    (∀ w y τ σ, RunsWithin D od w y τ σ → RunsWithin O O.inputTape (tagWord 2 w) y (k*(τ+w.length+1)) (k*(σ+w.length+1))) := by
  let Ms : Fin 3 → PrimitiveMachine := ![F,A,D]
  let os : (i : Fin 3) → Fin (Ms i).tapeCount := Fin.cases of₀ (Fin.cases oa (Fin.cases od (fun i => i.elim0)))
  obtain ⟨O,k,H⟩ := d4b_three_oracle_mux Ms os
  exact ⟨O,k,H 0,H 1,H 2⟩
end DetDLP.D4BFinish

open DetDLP DetDLP.D4BFinish DetDLP.D4Plan DetDLP.D4BBudget DetDLP.D4BEntry DetDLP.D4BOuter DetDLP.MachineComposition OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
set_option maxHeartbeats 800000 in
theorem solution (hscalar :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ'),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            ∃ w : List Bool,
              EncodesTruncPoly P ℓ' w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
                (polyBound K (β + desc.length) * (Told : ℝ) *
                  (2 : ℝ) ^ ((K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ)))
                (polyBound K (β + desc.length)))
    (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) (L₀ e s d : ℕ)
    (A F D : PrimitiveMachine) (oa : Fin A.tapeCount) (of₀ : Fin F.tapeCount) (od : Fin D.tapeCount)
    (small : ∀ x : Input C c, Nat.clog 2 x.S < L₀ → entry x E o → RunsWithin F of₀ (input x) (answer x) (polyBound s (size x)) (polyBound s (size x)))
    (large : ∀ x : Input C c, L₀ ≤ Nat.clog 2 x.S → entry x E o → ∃ P : Plan x, (∀ i < P.f.natDegree, P.f.coeff i = 0 ∨ P.f.coeff i = 1) ∧ Enumerates A oa e P ∧ Digits D od d P) :
    ∃ (M : PrimitiveMachine) (om : Fin M.tapeCount) (K : ℕ), ∀ x : Input C c, entry x E o → RunsWithin M om (input x) (answer x) (time x K) (polyBound K (size x)) := by
  obtain ⟨D',od',kD,scalar⟩ := D4BScalar.obtainCalls hscalar C c e d hC D od
  obtain ⟨D',od',kD,scalar⟩ := D4BScalar.obtainCalls hscalar C c e d hC D od
  obtain ⟨ks,smcap⟩ := smallCap C c s
  obtain ⟨kb,lgcap⟩ := d4b_outer_caps_uniform C c e
  obtain ⟨O,m,tagF,tagA,tagD⟩ := tagMux F A D' of₀ oa od'
  let h := max ks kb; let k := max s (max e kD)
  obtain ⟨j,budget⟩ := muxBudget m k h
  obtain ⟨a,rate⟩ := d4b_outer_rate_absorption C c hC
  obtain ⟨rK,rround⟩ := roundsBudget h (2*(e*a))
  obtain ⟨M,om,L,_,run⟩ := m89_polyT_oracle_loop (step L₀) (d4b_outer_step_poly _) O O.inputTape
  obtain ⟨K,done⟩ := compilerBudget L h j (max 2 rK)
  refine ⟨M,om,K,?_⟩; intro x en
  let n := D4Plan.size x; let H := np h n; let τ := time x j; let σ := polyBound j n
  have hcS : np ks n ≤ H := npK (le_max_left ..) _
  have hcB : np kb n ≤ H := npK (le_max_right ..) _
  have hpos : 0 ≤ R x := rpos x
  have ep := pow1 k hpos
  have hK (b : ℕ) (hb : b ≤ k) : polyBound b n ≤ polyBound k n := pbK hb n
  have muxCap {w y : List Bool} {tag : ℕ} {t z : ℝ} (hQ : w.length ≤ H) (ht : t ≤ time x k) (hs : z ≤ polyBound k n)
      (hh : RunsWithin O O.inputTape (tagWord tag w) y (m*(t+w.length+1)) (m*(z+w.length+1))) : RunsWithin O O.inputTape (tagWord tag w) y τ σ := by
    obtain ⟨q₁,q₂⟩ := budget n (R x) hpos
    have hhQ : (w.length:ℝ) ≤ H := by exact_mod_cast hQ
    apply runsWithin_mono hh
    · apply le_trans _ q₁; change _ ≤ (m:ℝ)*(time x k+(H:ℝ)+1); gcongr
    · apply le_trans _ q₂; change _ ≤ (m:ℝ)*(polyBound k n+(H:ℝ)+1); gcongr
  have execute (rounds : ℕ) (pos : 1 ≤ rounds) (cost : (rounds:ℝ) ≤ polyBound (max 2 rK) n*powR (max 2 rK) (R x))
      (tr : TraceAt L₀ O O.inputTape τ σ H (answer x) rounds (input x) []) : RunsWithin M om (input x) (answer x) (time x K) (polyBound K n) := by
    have hh := run τ σ (by unfold τ time polyBound; positivity) (by unfold σ polyBound; positivity) rounds H (input x) (answer x) pos tr
    obtain ⟨tm,sp⟩ := done n (R x) rounds H hpos le_rfl cost
    exact runsWithin_mono hh tm sp
  by_cases sm : Nat.clog 2 x.S < L₀
  · have hf := small x sm en
    obtain ⟨i,hq,hy,ho⟩ := smcap x hf
    have eq : polyBound s n ≤ time x k := (hK _ (le_max_left ..)).trans (le_mul_of_one_le_right (by unfold polyBound; positivity) ep)
    have cal := muxCap ((tagLen hq).trans hcS) eq (hK _ (le_max_left ..)) (tagF _ _ _ _ hf)
    apply execute 2 (by decide) _ (smallTrace L₀ H sm (i.trans hcS) (ho.trans hcS) ⟨cal,hq.trans hcS,hy.trans hcS⟩)
    apply le_trans _ (le_mul_of_one_le_right (by unfold polyBound; positivity) (pow1 _ hpos)); apply le_trans _ (pbK (le_max_left 2 rK) _); unfold polyBound; push_cast; nlinarith only [Nat.cast_nonneg (α:=ℝ) n, sq_nonneg (n:ℝ)]
  · have hh := Nat.le_of_not_gt sm
    obtain ⟨P,bin,he,hd⟩ := large x hh en
    obtain ⟨v,exactValue,caps,drun⟩ := scalar P he hd
    obtain ⟨ini,out,hdr,br,dg,hneed⟩ := lgcap x P he v caps
    have hdK : kD ≤ k := (le_max_right e kD).trans (le_max_right ..)
    have heK : e ≤ k := (le_max_left e kD).trans (le_max_right ..)
    have et : polyBound e n * (2:ℝ)^((e:ℝ)*((x.b:ℝ)/x.m)) ≤ time x k := by
      apply le_trans _ (timeK heK x); apply mul_le_mul_of_nonneg_left _ (by unfold polyBound; positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num); apply mul_le_mul_of_nonneg_left _ (by positivity); exact le_add_of_nonneg_right (by positivity)
    obtain ⟨ar,arr,cN,cD,_⟩ := he
    let B := ⌈powR (2*(e*a)) (R x)⌉₊
    have ab := (rate x).1
    let lam := (Nat.clog 2 x.S:ℝ)
    have digit : lam^(13/10:ℝ) ≤ a*R x := (le_add_of_nonneg_left (by positivity : (0:ℝ) ≤ x.b/(Nat.clog 2 x.S:ℝ)^(7/40:ℝ))).trans ab
    have nexp : (P.N:ℝ) ≤ powR (2*(e*a)) (R x) := cN.trans (expPow hpos (by push_cast; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ab (by positivity)))
    have dc (u : Fin P.N) : J P u^(P.R u).nV ≤ B := by
      have hb := (cD u).trans (expPow (a:=e*a) hpos (by push_cast; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left digit (by positivity)))
      exact_mod_cast hb.trans (Nat.le_ceil _)
    have hB : (B:ℝ) ≤ powR (2*(e*a)) (R x)+1 := (Nat.ceil_lt_add_one (by unfold powR; positivity)).le
    have G : BranchOracle P v O O.inputTape τ σ H B := by
      refine ⟨exactValue,dc,out.trans hcB,?_,?_⟩
      · intro u s; obtain ⟨hq,hy⟩ := br u s
        exact ⟨muxCap ((tagLen hq).trans hcB) et (hK _ heK) (tagA _ _ _ _ (arr u)),hq.trans hcB,hy.trans hcB⟩
      · intro u a s t; obtain ⟨hq,hy⟩ := dg u a s t
        exact ⟨muxCap ((tagLen hq).trans hcB) (timeK hdK x) (hK _ hdK) (tagD _ _ _ _ (drun u a)),hq.trans hcB,hy.trans hcB⟩
    obtain ⟨r,hr,hlen,tr⟩ := d4b_outer_ranked_transcript P v L₀ G hh bin (ini.trans hcB) (by
      intro b bl; obtain ⟨hq,hy⟩ := hdr b bl; exact ⟨muxCap ((tagLen hq).trans hcB) et (hK _ heK) (tagA _ _ _ _ ar),hq.trans hcB,hy.trans hcB⟩)
    apply execute r hr _ tr
    apply le_trans (by exact_mod_cast hlen : (r:ℝ) ≤ ((need P+3+P.N*(B+1):ℕ):ℝ))
    apply (rround n (R x) P.N B (need P) hpos nexp hB (hneed.trans hcB)).trans
    exact timeK (le_max_right 2 rK) x

