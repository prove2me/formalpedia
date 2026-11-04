-- Prove2me | solution 1 for FactorRMDP.Blackwell.proposition_6_1_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T23:17:31.877354+00:00
-- url     : https://prove2.me/submissions/54ff7636-8576-4f43-9bc9-6a4c2f73091a

import Mathlib
import Definitions.Def_FactorRMDP_Blackwell_Model

open Matrix Filter Topology

namespace P62Aux
open FactorRMDP.Blackwell

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] {r : ℕ}

/-- Maximum principle: if `λ L x ≤ x` componentwise with `L` row-stochastic, then `x ≥ 0`. -/
lemma nonneg_of_le (L : Matrix S S ℝ) (hL0 : ∀ s s', 0 ≤ L s s') (hL1 : ∀ s, ∑ s', L s s' = 1)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) (x : S → ℝ)
    (hx : ∀ s, lam * (L *ᵥ x) s ≤ x s) : ∀ s, 0 ≤ x s := by
  intro s
  haveI : Nonempty S := ⟨s⟩
  obtain ⟨s0, hs0⟩ := Finite.exists_min x
  have hL : x s0 ≤ (L *ᵥ x) s0 := by
    have : ∑ s', L s0 s' * x s0 ≤ ∑ s', L s0 s' * x s' :=
      Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hs0 s') (hL0 s0 s')
    rw [← Finset.sum_mul, hL1, one_mul] at this
    simpa [mulVec, dotProduct] using this
  have h2 := hx s0
  have : 0 ≤ x s0 := by nlinarith
  exact le_trans this (hs0 s)

lemma L_apply (M : Model S A r) (π : S → A → ℝ) (W : Fin r → S → ℝ) (s s' : S) :
    M.L π W s s' = ∑ i, M.T π s i * W i s' := by
  simp [Model.L, Matrix.mul_apply, FactorRMDP.ValueIter.wmat]

lemma L_mulVec (M : Model S A r) (π : S → A → ℝ) (W : Fin r → S → ℝ) (v : S → ℝ) (s : S) :
    (M.L π W *ᵥ v) s = ∑ i, M.T π s i * (W i ⬝ᵥ v) := by
  simp only [Model.L, ← Matrix.mulVec_mulVec]
  simp [mulVec, dotProduct, FactorRMDP.ValueIter.wmat]

lemma T_nonneg (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    (s : S) (i : Fin r) : 0 ≤ M.T π s i :=
  Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) (M.u_nonneg i s a)

lemma T_sum (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    (s : S) : ∑ i, M.T π s i = 1 := by
  simp only [Model.T]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.u_sum, mul_one]
  exact (hπ s).2

lemma L_nonneg (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {W : Fin r → S → ℝ} (hW : ∀ i, W i ∈ stdSimplex ℝ S) (s s' : S) : 0 ≤ M.L π W s s' := by
  rw [L_apply]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (T_nonneg M hπ s i) ((hW i).1 s')

lemma L_sum (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {W : Fin r → S → ℝ} (hW : ∀ i, W i ∈ stdSimplex ℝ S) (s : S) : ∑ s', M.L π W s s' = 1 := by
  simp_rw [L_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hW _).2, mul_one]
  exact T_sum M hπ s

lemma norm_mulVec_le (L : Matrix S S ℝ) (hL0 : ∀ s s', 0 ≤ L s s') (hL1 : ∀ s, ∑ s', L s s' = 1)
    (x : S → ℝ) : ‖L *ᵥ x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun s => ?_
  rw [Real.norm_eq_abs]
  calc |(L *ᵥ x) s| = |∑ s', L s s' * x s'| := rfl
    _ ≤ ∑ s', |L s s' * x s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', L s s' * ‖x‖ := Finset.sum_le_sum fun s' _ => by
        rw [abs_mul, abs_of_nonneg (hL0 s s')]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x s')
          (hL0 s s')
    _ = ‖x‖ := by rw [← Finset.sum_mul, hL1, one_mul]

lemma norm_pow_mulVec_le (L : Matrix S S ℝ) (hL0 : ∀ s s', 0 ≤ L s s')
    (hL1 : ∀ s, ∑ s', L s s' = 1) (x : S → ℝ) (t : ℕ) : ‖(L ^ t) *ᵥ x‖ ≤ ‖x‖ := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact (norm_mulVec_le L hL0 hL1 _).trans ih

/-- The value is the sum of the discounted series, and satisfies `v = r_π + λ L v`. -/
lemma value_eq (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {W : Fin r → S → ℝ} (hW : ∀ i, W i ∈ stdSimplex ℝ S) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    M.value lam π W = M.rpi π + lam • (M.L π W *ᵥ M.value lam π W) := by
  set L := M.L π W
  have hL0 := L_nonneg M hπ hW
  have hL1 := L_sum M hπ hW
  set f : ℕ → S → ℝ := fun t => lam ^ t • ((L ^ t) *ᵥ M.rpi π) with hf
  have hsum : Summable f := by
    refine Summable.of_norm_bounded (g := fun t => lam ^ t * ‖M.rpi π‖)
      ((summable_geometric_of_lt_one h0 h1).mul_right _) fun t => ?_
    simp only [f, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (norm_pow_mulVec_le L hL0 hL1 _ t) (pow_nonneg h0 t)
  have hv : HasSum f (M.value lam π W) := hsum.hasSum
  let g : (S → ℝ) →L[ℝ] (S → ℝ) := LinearMap.toContinuousLinearMap (mulVecLin (lam • L))
  have hg : ∀ x, g x = lam • (L *ᵥ x) := fun x => by
    simp [g, smul_mulVec]
  have h2 : HasSum (fun t => f (t + 1)) (g (M.value lam π W)) := by
    have := hv.mapL g
    convert this using 1
    funext t
    simp only [Function.comp, hg, f, pow_succ', ← mulVec_mulVec, mulVec_smul, smul_smul]
  have h3 : HasSum (fun t => f (t + 1)) (M.value lam π W - ∑ i ∈ Finset.range 1, f i) :=
    (hasSum_nat_add_iff' 1).mpr hv
  have h4 := h3.unique h2
  simp only [Finset.range_one, Finset.sum_singleton, f, pow_zero, one_smul, hg] at h4
  rw [← h4]
  simp

lemma comp_le (L : Matrix S S ℝ) (hL0 : ∀ s s', 0 ≤ L s s') (hL1 : ∀ s, ∑ s', L s s' = 1)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) (a b c : S → ℝ)
    (ha : ∀ s, c s + lam * (L *ᵥ a) s ≤ a s) (hb : ∀ s, b s ≤ c s + lam * (L *ᵥ b) s) :
    ∀ s, b s ≤ a s := by
  have := nonneg_of_le L hL0 hL1 h0 h1 (a - b) fun s => by
    rw [mulVec_sub]
    simp only [Pi.sub_apply]
    have := ha s; have := hb s
    nlinarith
  intro s
  have := this s
  simp only [Pi.sub_apply] at this
  linarith

lemma rpi_nonneg (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    (s : S) : 0 ≤ M.rpi π s :=
  Finset.sum_nonneg fun a _ => mul_nonneg ((hπ s).1 a) (M.rew_nonneg s a)

lemma value_eq_apply (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {W : Fin r → S → ℝ} (hW : ∀ i, W i ∈ stdSimplex ℝ S) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1)
    (s : S) :
    M.value lam π W s = M.rpi π s + lam * (M.L π W *ᵥ M.value lam π W) s := by
  have := congrFun (value_eq M hπ hW h0 h1) s
  simpa using this

lemma value_nonneg (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {W : Fin r → S → ℝ} (hW : ∀ i, W i ∈ stdSimplex ℝ S) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1)
    (s : S) : 0 ≤ M.value lam π W s := by
  have hz := comp_le (M.L π W) (L_nonneg M hπ hW) (L_sum M hπ hW) h0 h1 (M.value lam π W) 0 0
    (fun s => by rw [value_eq_apply M hπ hW h0 h1 s]; simp [rpi_nonneg M hπ s])
    (fun s => by simp)
  simpa using hz s

lemma eq_value (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {W : Fin r → S → ℝ} (hW : ∀ i, W i ∈ stdSimplex ℝ S) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1)
    (x : S → ℝ) (hx : ∀ s, x s = M.rpi π s + lam * (M.L π W *ᵥ x) s) : x = M.value lam π W := by
  have e := value_eq_apply M hπ hW h0 h1
  funext s
  exact le_antisymm
    (comp_le _ (L_nonneg M hπ hW) (L_sum M hπ hW) h0 h1 _ x (M.rpi π)
      (fun s => (e s).ge) (fun s => (hx s).le) s)
    (comp_le _ (L_nonneg M hπ hW) (L_sum M hπ hW) h0 h1 x _ (M.rpi π)
      (fun s => (hx s).ge) (fun s => (e s).le) s)

lemma R_nonneg (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {W : Fin r → S → ℝ} (hW : ∀ i, W i ∈ stdSimplex ℝ S) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    0 ≤ M.R lam π W :=
  Finset.sum_nonneg fun s _ => mul_nonneg (M.p0_mem.1 s) (value_nonneg M hπ hW h0 h1 s)

lemma R_le (M : Model S A r) {π π' : S → A → ℝ} {W W' : Fin r → S → ℝ} {lam : ℝ}
    (h : ∀ s, M.value lam π W s ≤ M.value lam π' W' s) : M.R lam π W ≤ M.R lam π' W' :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (M.p0_mem.1 s)

/-- Under Krein–Milman with finitely many extreme points, the minimum of a linear functional over a
factor set is attained among its extreme points. -/
lemma exists_ext_le (M : Model S A r) (i : Fin r)
    (hext : (Set.extremePoints ℝ (M.factorSet i)).Finite) (v : S → ℝ) {w : S → ℝ}
    (hw : w ∈ M.factorSet i) : ∃ e ∈ Set.extremePoints ℝ (M.factorSet i), e ⬝ᵥ v ≤ w ⬝ᵥ v := by
  have hcomp : IsCompact (M.factorSet i) := M.W_compact.image (continuous_apply i)
  have hconv : Convex ℝ (M.factorSet i) :=
    M.W_convex.is_linear_image (LinearMap.proj (R := ℝ) (φ := fun _ : Fin r => S → ℝ) i).isLinear
  have hKM := closure_convexHull_extremePoints hcomp hconv
  rw [(hext.isClosed_convexHull (𝕜 := ℝ)).closure_eq] at hKM
  let f : (S → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => x ⬝ᵥ v
      map_add' := fun x y => add_dotProduct x y v
      map_smul' := fun c x => by simp [smul_dotProduct] }
  have hf : ConcaveOn ℝ Set.univ f := f.concaveOn convex_univ
  rw [← hKM] at hw
  obtain ⟨e, he, hle⟩ := hf.exists_le_of_mem_convexHull (Set.subset_univ _) hw
  exact ⟨e, he, hle⟩

lemma ext_nonempty (M : Model S A r) (i : Fin r)
    (hext : (Set.extremePoints ℝ (M.factorSet i)).Finite) :
    (Set.extremePoints ℝ (M.factorSet i)).Nonempty := by
  obtain ⟨W, hW⟩ := M.W_nonempty
  obtain ⟨e, he, -⟩ := exists_ext_le M i hext 0 ⟨W, hW, rfl⟩
  exact ⟨e, he⟩

lemma policy_avg (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    (lam : ℝ) (W : Fin r → S → ℝ) (v : S → ℝ)
    (hb : ∀ s a, M.rew s a + lam * ∑ i, M.u i s a * (W i ⬝ᵥ v) ≤ v s) (s : S) :
    M.rpi π s + lam * (M.L π W *ᵥ v) s ≤ v s := by
  rw [L_mulVec]
  have : M.rpi π s + lam * ∑ i, M.T π s i * (W i ⬝ᵥ v)
      = ∑ a, π s a * (M.rew s a + lam * ∑ i, M.u i s a * (W i ⬝ᵥ v)) := by
    simp only [Model.rpi, Model.T, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  calc ∑ a, π s a * (M.rew s a + lam * ∑ i, M.u i s a * (W i ⬝ᵥ v))
      ≤ ∑ a, π s a * v s := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hb s a) ((hπ s).1 a)
    _ = v s := by rw [← Finset.sum_mul, (hπ s).2, one_mul]

/-- Sufficient condition for a robust solution at a fixed discount. -/
theorem key (M : Model S A r) (hext : ∀ i, (Set.extremePoints ℝ (M.factorSet i)).Finite)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (π : S → A → ℝ)
    (hπ : π ∈ FactorRMDP.ValueIter.Policies S A) (W : Fin r → S → ℝ) (hW : W ∈ M.Wset)
    (ha : ∀ i, ∀ e ∈ Set.extremePoints ℝ (M.factorSet i),
      W i ⬝ᵥ M.value lam π W ≤ e ⬝ᵥ M.value lam π W)
    (hb : ∀ s a, M.rew s a + lam * ∑ i, M.u i s a * (W i ⬝ᵥ M.value lam π W) ≤ M.value lam π W s) :
    M.IsRobustSolution lam π W := by
  set v := M.value lam π W with hv
  have hWs := M.W_simplex W hW
  have ha' : ∀ i, ∀ w ∈ M.factorSet i, W i ⬝ᵥ v ≤ w ⬝ᵥ v := fun i w hw => by
    obtain ⟨e, he, hle⟩ := exists_ext_le M i (hext i) v hw
    exact (ha i e he).trans hle
  have hleast : IsLeast (M.evalValues lam π) (M.R lam π W) := by
    refine ⟨⟨W, hW, rfl⟩, ?_⟩
    rintro _ ⟨W', hW', rfl⟩
    have hW's := M.W_simplex W' hW'
    apply R_le
    refine comp_le (M.L π W') (L_nonneg M hπ hW's) (L_sum M hπ hW's) h0.le h1 _ _ (M.rpi π)
      (fun s => (value_eq_apply M hπ hW's h0.le h1 s).ge) (fun s => ?_)
    rw [value_eq_apply M hπ hWs h0.le h1 s, ← hv, L_mulVec, L_mulVec]
    gcongr with i
    · exact T_nonneg M hπ s i
    · exact ha' i (W' i) ⟨W', hW', rfl⟩
  have hz : ∀ π' ∈ FactorRMDP.ValueIter.Policies S A, ∀ W' ∈ M.Wset, M.z lam π' ≤ M.R lam π' W' :=
    fun π' hπ' W' hW' => csInf_le ⟨0, by
      rintro _ ⟨W'', hW'', rfl⟩
      exact R_nonneg M hπ' (M.W_simplex W'' hW'') h0.le h1⟩ ⟨W', hW', rfl⟩
  have hzπ : M.z lam π = M.R lam π W := hleast.csInf_eq
  refine ⟨hπ, hW, ⟨⟨π, hπ, rfl⟩, ?_⟩, hleast⟩
  rintro _ ⟨π', hπ', rfl⟩
  refine (hz π' hπ' W hW).trans ?_
  rw [hzπ]
  apply R_le
  exact comp_le (M.L π' W) (L_nonneg M hπ' hWs) (L_sum M hπ' hWs) h0.le h1 v _ (M.rpi π')
    (policy_avg M hπ' lam W v hb) (fun s => (value_eq_apply M hπ' hWs h0.le h1 s).le)

/-- The deterministic policy of a decision rule `d`. -/
def pol (d : S → A) : S → A → ℝ := fun s a => if a = d s then 1 else 0

lemma pol_mem (d : S → A) : pol d ∈ FactorRMDP.ValueIter.Policies S A := fun s =>
  ⟨fun a => by unfold pol; split_ifs <;> norm_num, by simp [pol]⟩

lemma pol_det (d : S → A) : FactorRMDP.ValueIter.IsDeterministic (pol d) := ⟨d, fun _ _ => rfl⟩

lemma rpi_pol (M : Model S A r) (d : S → A) (s : S) : M.rpi (pol d) s = M.rew s (d s) := by
  simp [Model.rpi, pol]

lemma T_pol (M : Model S A r) (d : S → A) (s : S) (i : Fin r) :
    M.T (pol d) s i = M.u i s (d s) := by
  simp [Model.T, pol]

lemma factorSet_simplex (M : Model S A r) (i : Fin r) {w : S → ℝ} (hw : w ∈ M.factorSet i) :
    w ∈ stdSimplex ℝ S := by
  obtain ⟨W, hW, rfl⟩ := hw
  exact M.W_simplex W hW i

lemma dot_le_dist {e : S → ℝ} (he : e ∈ stdSimplex ℝ S) (v v' : S → ℝ) :
    e ⬝ᵥ v ≤ e ⬝ᵥ v' + dist v v' := by
  have : e ⬝ᵥ v - e ⬝ᵥ v' ≤ dist v v' := by
    rw [← dotProduct_sub]
    calc e ⬝ᵥ (v - v') = ∑ s, e s * (v s - v' s) := rfl
      _ ≤ ∑ s, e s * dist v v' := Finset.sum_le_sum fun s _ => by
          apply mul_le_mul_of_nonneg_left _ (he.1 s)
          calc v s - v' s ≤ |v s - v' s| := le_abs_self _
            _ = dist (v s) (v' s) := (Real.dist_eq _ _).symm
            _ ≤ dist v v' := dist_le_pi_dist v v' s
      _ = dist v v' := by rw [← Finset.sum_mul, he.2, one_mul]
  linarith

variable (M : Model S A r) (hext : ∀ i, (Set.extremePoints ℝ (M.factorSet i)).Finite)

noncomputable def extF (i : Fin r) : Finset (S → ℝ) := (hext i).toFinset

lemma extF_nonempty (i : Fin r) : (extF M hext i).Nonempty := by
  obtain ⟨e, he⟩ := ext_nonempty M i (hext i)
  exact ⟨e, (Set.Finite.mem_toFinset _).2 he⟩

lemma mem_extF {i : Fin r} {e : S → ℝ} : e ∈ extF M hext i ↔ e ∈ Set.extremePoints ℝ (M.factorSet i) :=
  Set.Finite.mem_toFinset _

noncomputable def mm (i : Fin r) (v : S → ℝ) : ℝ :=
  (extF M hext i).inf' (extF_nonempty M hext i) (fun e => e ⬝ᵥ v)

noncomputable def FF [Nonempty A] (lam : ℝ) (v : S → ℝ) : S → ℝ := fun s =>
  Finset.univ.sup' Finset.univ_nonempty (fun a => M.rew s a + lam * ∑ i, M.u i s a * mm M hext i v)

lemma mm_le (i : Fin r) (v v' : S → ℝ) : mm M hext i v ≤ mm M hext i v' + dist v v' := by
  have : mm M hext i v - dist v v' ≤ mm M hext i v' := by
    refine Finset.le_inf' _ _ fun e he => ?_
    have h1 : mm M hext i v ≤ e ⬝ᵥ v := Finset.inf'_le _ he
    have h2 := dot_le_dist (factorSet_simplex M i
      (extremePoints_subset ((mem_extF M hext).1 he))) v v'
    linarith
  linarith

lemma FF_le [Nonempty A] {lam : ℝ} (h0 : 0 ≤ lam) (v v' : S → ℝ) (s : S) :
    FF M hext lam v s ≤ FF M hext lam v' s + lam * dist v v' := by
  have : FF M hext lam v s - lam * dist v v' ≤ FF M hext lam v' s := by
    rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun a _ => ?_
    have hle : ∑ i, M.u i s a * mm M hext i v ≤ ∑ i, M.u i s a * mm M hext i v' + dist v v' := by
      have : ∑ i, M.u i s a * mm M hext i v ≤ ∑ i, M.u i s a * (mm M hext i v' + dist v v') :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (mm_le M hext i v v') (M.u_nonneg i s a)
      simpa [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.u_sum] using this
    have h2 : M.rew s a + lam * ∑ i, M.u i s a * mm M hext i v' ≤ FF M hext lam v' s :=
      Finset.le_sup' (fun a => M.rew s a + lam * ∑ i, M.u i s a * mm M hext i v') (Finset.mem_univ a)
    nlinarith
  linarith

lemma FF_contracting [Nonempty A] {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ContractingWith (Real.toNNReal lam) (FF M hext lam) := by
  refine ⟨by simpa using h1, LipschitzWith.of_dist_le_mul fun v v' => ?_⟩
  rw [Real.coe_toNNReal _ h0]
  refine (dist_pi_le_iff (mul_nonneg h0 dist_nonneg)).2 fun s => ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  have := FF_le M hext h0 v v' s
  have := FF_le M hext h0 v' v s
  rw [dist_comm v' v] at this
  constructor <;> linarith

/-- For every discount there is a candidate pair satisfying the sufficient conditions. -/
theorem exists_good [Nonempty A] (hext : ∀ i, (Set.extremePoints ℝ (M.factorSet i)).Finite)
    (hR : M.IsRRect) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∃ d : S → A, ∃ W : Fin r → S → ℝ, (∀ i, W i ∈ Set.extremePoints ℝ (M.factorSet i)) ∧
      (∀ i, ∀ e ∈ Set.extremePoints ℝ (M.factorSet i),
        W i ⬝ᵥ M.value lam (pol d) W ≤ e ⬝ᵥ M.value lam (pol d) W) ∧
      (∀ s a, M.rew s a + lam * ∑ i, M.u i s a * (W i ⬝ᵥ M.value lam (pol d) W)
        ≤ M.value lam (pol d) W s) := by
  have hc := FF_contracting M hext h0.le h1
  set v := ContractingWith.fixedPoint (FF M hext lam) hc with hvdef
  have hv : FF M hext lam v = v := ContractingWith.fixedPoint_isFixedPt (f := FF M hext lam) hc
  set f : S → A → ℝ := fun s a => M.rew s a + lam * ∑ i, M.u i s a * mm M hext i v with hf
  have hd : ∀ s, ∃ a ∈ (Finset.univ : Finset A), ∀ a' ∈ (Finset.univ : Finset A), f s a' ≤ f s a :=
    fun s => Finset.exists_max_image _ _ Finset.univ_nonempty
  choose d _ hd using hd
  have hW : ∀ i, ∃ e ∈ extF M hext i, ∀ e' ∈ extF M hext i, e ⬝ᵥ v ≤ e' ⬝ᵥ v :=
    fun i => Finset.exists_min_image _ _ (extF_nonempty M hext i)
  choose W hWm hW using hW
  have hmm : ∀ i, mm M hext i v = W i ⬝ᵥ v := fun i =>
    le_antisymm (Finset.inf'_le _ (hWm i)) (Finset.le_inf' _ _ fun e he => hW i e he)
  have hFF : ∀ s, v s = f s (d s) := fun s => by
    have : FF M hext lam v s = f s (d s) :=
      le_antisymm (Finset.sup'_le _ _ fun a _ => hd s a (Finset.mem_univ a))
        (Finset.le_sup' (f s) (Finset.mem_univ _))
    rw [← this, hv]
  have hWext : ∀ i, W i ∈ Set.extremePoints ℝ (M.factorSet i) := fun i => (mem_extF M hext).1 (hWm i)
  have hWs : ∀ i, W i ∈ stdSimplex ℝ S := fun i =>
    factorSet_simplex M i (extremePoints_subset (hWext i))
  have hval : v = M.value lam (pol d) W := by
    refine eq_value M (pol_mem d) hWs h0.le h1 v fun s => ?_
    rw [hFF s, rpi_pol, L_mulVec]
    simp only [hf, T_pol, hmm]
  refine ⟨d, W, hWext, fun i e he => ?_, fun s a => ?_⟩ <;> rw [← hval]
  · exact hW i e ((mem_extF M hext).2 he)
  · rw [hFF s]
    have := hd s a (Finset.mem_univ a)
    simpa only [hf, hmm] using this

lemma W_mem (hR : M.IsRRect) (W : Fin r → S → ℝ)
    (hW : ∀ i, W i ∈ Set.extremePoints ℝ (M.factorSet i)) : W ∈ M.Wset := by
  rw [hR]
  exact Set.mem_univ_pi.2 fun i => extremePoints_subset (hW i)

open Polynomial in
lemma poly_dich (P : ℝ[X]) :
    (∀ᶠ t in 𝓝[<] (1 : ℝ), 0 ≤ P.eval t) ∨ (∀ᶠ t in 𝓝[<] (1 : ℝ), P.eval t < 0) := by
  by_cases hP : P = 0
  · left; simp [hP]
  have hZ : {x : ℝ | P.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hP
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), P.eval t ≠ 0 := by
    have h1 : ({x : ℝ | P.IsRoot x} \ {1})ᶜ ∈ 𝓝 (1 : ℝ) :=
      (hZ.diff).isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [mem_nhdsWithin_of_mem_nhds h1, self_mem_nhdsWithin] with t ht ht1
    intro h0
    exact ht ⟨h0, ne_of_lt ht1⟩
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
  have hl1 : l < 1 := hl
  have hIoo : Set.Ioo l 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT hl1
  have hcont : ContinuousOn (fun t => P.eval t) (Set.Ioo l 1) := P.continuous.continuousOn
  have hm : (l + 1) / 2 ∈ Set.Ioo l 1 := ⟨by linarith, by linarith⟩
  have noroot : ∀ a ∈ Set.Ioo l 1, ∀ b ∈ Set.Ioo l 1, P.eval a ≤ 0 → 0 ≤ P.eval b → False := by
    intro a ha b hb hab hb0
    obtain ⟨x, hx, hx0⟩ := isPreconnected_Ioo.intermediate_value ha hb hcont ⟨hab, hb0⟩
    exact hsub hx hx0
  by_cases h : 0 ≤ P.eval ((l + 1) / 2)
  · left
    filter_upwards [hIoo] with t ht
    by_contra hneg
    exact noroot t ht _ hm (le_of_lt (not_le.1 hneg)) h
  · right
    filter_upwards [hIoo] with t ht
    by_contra hneg
    exact noroot _ hm t ht (le_of_lt (not_le.1 h)) (not_lt.1 hneg)

/-- The polynomial matrix `1 - X L`. -/
noncomputable def polyM (L : Matrix S S ℝ) : Matrix S S (Polynomial ℝ) :=
  1 - (Polynomial.X : Polynomial ℝ) • L.map Polynomial.C

lemma eval_polyM (L : Matrix S S ℝ) (t : ℝ) :
    (Polynomial.evalRingHom t).mapMatrix (polyM L) = 1 - t • L := by
  ext i j
  simp [polyM, Matrix.one_apply]
  split_ifs <;> simp [mul_comm]

lemma det_ne (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {W : Fin r → S → ℝ} (hW : ∀ i, W i ∈ stdSimplex ℝ S) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    (1 - t • M.L π W).det ≠ 0 := by
  intro h
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hx' : ∀ s, x s = 0 + t * (M.L π W *ᵥ x) s := fun s => by
    have := congrFun hx s
    simp [sub_mulVec, smul_mulVec] at this
    linarith
  apply hx0
  funext s
  exact le_antisymm
    (comp_le _ (L_nonneg M hπ hW) (L_sum M hπ hW) h0 h1 0 x 0 (fun s => by simp)
      (fun s => (hx' s).le) s)
    (comp_le _ (L_nonneg M hπ hW) (L_sum M hπ hW) h0 h1 x 0 0 (fun s => (hx' s).ge)
      (fun s => by simp) s)

lemma rat_dich (M : Model S A r) {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {W : Fin r → S → ℝ} (hW : ∀ i, W i ∈ stdSimplex ℝ S) (α : Polynomial ℝ) (β : S → Polynomial ℝ) :
    (∀ᶠ t in 𝓝[<] (1 : ℝ), 0 ≤ α.eval t + ∑ s, (β s).eval t * M.value t π W s) ∨
    (∀ᶠ t in 𝓝[<] (1 : ℝ), ¬ 0 ≤ α.eval t + ∑ s, (β s).eval t * M.value t π W s) := by
  set L := M.L π W
  set D := (polyM L).det
  set N : S → Polynomial ℝ := (polyM L).adjugate *ᵥ (fun j => Polynomial.C (M.rpi π j))
  set P := (α * D + ∑ s, β s * N s) * D
  have key : ∀ t, 0 < t → t < 1 →
      P.eval t = (1 - t • L).det ^ 2 * (α.eval t + ∑ s, (β s).eval t * M.value t π W s) := by
    intro t h0 h1
    have hD : D.eval t = (1 - t • L).det := by
      rw [← eval_polyM]
      exact RingHom.map_det (Polynomial.evalRingHom t) (polyM L)
    have hBv : (1 - t • L) *ᵥ M.value t π W = M.rpi π := by
      have := value_eq M hπ hW h0.le h1
      rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_iff_eq_add]
      exact this
    have hN : ∀ s, (N s).eval t = (1 - t • L).det * M.value t π W s := by
      intro s
      have h1 : (N s).eval t = ((1 - t • L).adjugate *ᵥ M.rpi π) s := by
        rw [← eval_polyM, ← RingHom.map_adjugate]
        simp [N, mulVec, dotProduct, Polynomial.eval_finsetSum]
      rw [h1, ← hBv, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
      simp
    simp only [P, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_finsetSum, hD, hN]
    have : ∑ x, Polynomial.eval t (β x) * ((1 - t • L).det * M.value t π W x)
        = (1 - t • L).det * ∑ s, Polynomial.eval t (β s) * M.value t π W s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this]
    ring
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t ∧ t < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact ht
  have iff : ∀ t, 0 < t → t < 1 →
      (0 ≤ α.eval t + ∑ s, (β s).eval t * M.value t π W s ↔ 0 ≤ P.eval t) := by
    intro t h0 h1
    rw [key t h0 h1]
    have hpos : 0 < (1 - t • L).det ^ 2 := by
      have := det_ne M hπ hW h0.le h1
      positivity
    constructor
    · intro h; exact mul_nonneg hpos.le h
    · intro h; exact nonneg_of_mul_nonneg_right (by linarith) hpos
  rcases poly_dich P with h | h
  · left
    filter_upwards [h, hev] with t ht ht'
    exact (iff t ht'.1 ht'.2).2 ht
  · right
    filter_upwards [h, hev] with t ht ht'
    rw [iff t ht'.1 ht'.2]
    exact not_le.2 ht

lemma dich_all {ι : Type*} [Finite ι] {l : Filter ℝ} (p : ι → ℝ → Prop)
    (h : ∀ i, (∀ᶠ t in l, p i t) ∨ (∀ᶠ t in l, ¬ p i t)) :
    (∀ᶠ t in l, ∀ i, p i t) ∨ (∀ᶠ t in l, ¬ ∀ i, p i t) := by
  by_cases hall : ∀ i, ∀ᶠ t in l, p i t
  · exact Or.inl (Filter.eventually_all.2 hall)
  · simp only [not_forall] at hall
    obtain ⟨i, hi⟩ := hall
    refine Or.inr ?_
    have := (h i).resolve_left hi
    filter_upwards [this] with t ht hall using ht (hall i)

lemma dich_and {l : Filter ℝ} (p q : ℝ → Prop)
    (hp : (∀ᶠ t in l, p t) ∨ (∀ᶠ t in l, ¬ p t)) (hq : (∀ᶠ t in l, q t) ∨ (∀ᶠ t in l, ¬ q t)) :
    (∀ᶠ t in l, p t ∧ q t) ∨ (∀ᶠ t in l, ¬ (p t ∧ q t)) := by
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · exact Or.inl (hp.and hq)
    · exact Or.inr (hq.mono fun t ht h => ht h.2)
  · exact Or.inr (hp.mono fun t ht h => ht h.1)

lemma dich_of_iff (p f : ℝ → Prop) (hpf : ∀ t, 0 < t → t < 1 → (p t ↔ f t))
    (hf : (∀ᶠ t in 𝓝[<] (1 : ℝ), f t) ∨ (∀ᶠ t in 𝓝[<] (1 : ℝ), ¬ f t)) :
    (∀ᶠ t in 𝓝[<] (1 : ℝ), p t) ∨ (∀ᶠ t in 𝓝[<] (1 : ℝ), ¬ p t) := by
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), 0 < t ∧ t < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact ht
  rcases hf with hf | hf
  · exact Or.inl (by filter_upwards [hf, hev] with t ht ht' using (hpf t ht'.1 ht'.2).2 ht)
  · exact Or.inr (by filter_upwards [hf, hev] with t ht ht' using fun h => ht ((hpf t ht'.1 ht'.2).1 h))

end P62Aux


namespace P61Aux
open FactorRMDP.Blackwell P62Aux

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A] {r : ℕ}
variable (M : Model S A r)

lemma minFactor_spec (i : Fin r) (v : S → ℝ) :
    ∃ w ∈ M.factorSet i, w ⬝ᵥ v = M.minFactor i v ∧ ∀ w' ∈ M.factorSet i, M.minFactor i v ≤ w' ⬝ᵥ v := by
  have hcomp : IsCompact (M.factorSet i) := M.W_compact.image (continuous_apply i)
  obtain ⟨W, hW⟩ := M.W_nonempty
  have hne : (M.factorSet i).Nonempty := ⟨W i, W, hW, rfl⟩
  have hcont : Continuous fun w : S → ℝ => w ⬝ᵥ v :=
    continuous_finset_sum _ fun s _ => (continuous_apply s).mul continuous_const
  obtain ⟨w, hw, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
  have hl : IsLeast ((fun w => w ⬝ᵥ v) '' M.factorSet i) (w ⬝ᵥ v) :=
    ⟨⟨w, hw, rfl⟩, by rintro _ ⟨w', hw', rfl⟩; exact hmin hw'⟩
  have heq : M.minFactor i v = w ⬝ᵥ v := hl.csInf_eq
  exact ⟨w, hw, heq.symm, fun w' hw' => heq ▸ hmin hw'⟩

lemma minFactor_le (i : Fin r) (v v' : S → ℝ) : M.minFactor i v ≤ M.minFactor i v' + dist v v' := by
  obtain ⟨w', hw', heq', _⟩ := minFactor_spec M i v'
  obtain ⟨_, _, _, hle⟩ := minFactor_spec M i v
  have := dot_le_dist (factorSet_simplex M i hw') v v'
  have := hle w' hw'
  linarith

/-- the operator `F` of the definition is a contraction -/
lemma F_le [Nonempty A] {lam : ℝ} (h0 : 0 ≤ lam) (v v' : S → ℝ) (s : S) :
    M.F lam v s ≤ M.F lam v' s + lam * dist v v' := by
  have : M.F lam v s - lam * dist v v' ≤ M.F lam v' s := by
    rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun a _ => ?_
    have hle : ∑ i, M.u i s a * M.minFactor i v ≤ ∑ i, M.u i s a * M.minFactor i v' + dist v v' := by
      have : ∑ i, M.u i s a * M.minFactor i v ≤ ∑ i, M.u i s a * (M.minFactor i v' + dist v v') :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (minFactor_le M i v v') (M.u_nonneg i s a)
      simpa [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.u_sum] using this
    have h2 : M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i v' ≤ M.F lam v' s :=
      Finset.le_sup' (fun a => M.rew s a + lam * ∑ i, M.u i s a * M.minFactor i v') (Finset.mem_univ a)
    nlinarith
  linarith

lemma F_contracting [Nonempty A] {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ContractingWith (Real.toNNReal lam) (M.F lam) := by
  refine ⟨by simpa using h1, LipschitzWith.of_dist_le_mul fun v v' => ?_⟩
  rw [Real.coe_toNNReal _ h0]
  refine (dist_pi_le_iff (mul_nonneg h0 dist_nonneg)).2 fun s => ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  have := F_le M h0 v v' s
  have := F_le M h0 v' v s
  rw [dist_comm v' v] at this
  constructor <;> linarith

/-- Policy-evaluation operator `G(v) = r_π + λ T_π (minFactor_i v)_i`. -/
noncomputable def G (lam : ℝ) (π : S → A → ℝ) (v : S → ℝ) : S → ℝ := fun s =>
  M.rpi π s + lam * ∑ i, M.T π s i * M.minFactor i v

lemma G_contracting {π : S → A → ℝ} (hπ : π ∈ FactorRMDP.ValueIter.Policies S A)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ContractingWith (Real.toNNReal lam) (G M lam π) := by
  refine ⟨by simpa using h1, LipschitzWith.of_dist_le_mul fun v v' => ?_⟩
  rw [Real.coe_toNNReal _ h0]
  refine (dist_pi_le_iff (mul_nonneg h0 dist_nonneg)).2 fun s => ?_
  have hle : ∀ v v' : S → ℝ, G M lam π v s ≤ G M lam π v' s + lam * dist v v' := by
    intro v v'
    have : ∑ i, M.T π s i * M.minFactor i v ≤ ∑ i, M.T π s i * M.minFactor i v' + dist v v' := by
      have : ∑ i, M.T π s i * M.minFactor i v ≤ ∑ i, M.T π s i * (M.minFactor i v' + dist v v') :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (minFactor_le M i v v') (T_nonneg M hπ s i)
      simpa [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, T_sum M hπ s] using this
    simp only [G]
    nlinarith
  rw [Real.dist_eq, abs_sub_le_iff]
  have := hle v v'
  have := hle v' v
  rw [dist_comm v' v] at this
  constructor <;> linarith

/-- Under r-rectangularity, every policy has a factor matrix minimizing its value at every state. -/
theorem exists_pointwise_min (hR : M.IsRRect) {π : S → A → ℝ}
    (hπ : π ∈ FactorRMDP.ValueIter.Policies S A) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    ∃ W ∈ M.Wset, ∀ W₀ ∈ M.Wset, ∀ s, M.value lam π W s ≤ M.value lam π W₀ s := by
  have hc := G_contracting M hπ h0 h1
  set v := ContractingWith.fixedPoint (G M lam π) hc
  have hv : G M lam π v = v := ContractingWith.fixedPoint_isFixedPt (f := G M lam π) hc
  choose W hWm hWeq _ using fun i => minFactor_spec M i v
  have hWmem : W ∈ M.Wset := by rw [hR]; exact Set.mem_univ_pi.2 hWm
  have hWs := M.W_simplex W hWmem
  have hval : v = M.value lam π W := by
    refine eq_value M hπ hWs h0 h1 v fun s => ?_
    rw [L_mulVec]
    conv_lhs => rw [← hv]
    simp only [G, hWeq]
  refine ⟨W, hWmem, fun W₀ hW₀ s => ?_⟩
  rw [← hval]
  have hW₀s := M.W_simplex W₀ hW₀
  refine comp_le (M.L π W₀) (L_nonneg M hπ hW₀s) (L_sum M hπ hW₀s) h0 h1 _ v (M.rpi π)
    (fun s => (value_eq_apply M hπ hW₀s h0 h1 s).ge) (fun s => ?_) s
  rw [L_mulVec]
  conv_lhs => rw [← hv]
  simp only [G]
  gcongr with i
  · exact T_nonneg M hπ s i
  · obtain ⟨_, _, _, hle⟩ := minFactor_spec M i v
    exact hle _ ⟨W₀, hW₀, rfl⟩

lemma eq_of_R_le (hp0 : ∀ s, 0 < M.p0 s) {x y : S → ℝ} (hxy : ∀ s, x s ≤ y s)
    (h : M.p0 ⬝ᵥ y ≤ M.p0 ⬝ᵥ x) : ∀ s, y s = x s := by
  have hsum : ∑ s, M.p0 s * (y s - x s) ≤ 0 := by
    have : M.p0 ⬝ᵥ y - M.p0 ⬝ᵥ x ≤ 0 := by linarith
    simpa [dotProduct, mul_sub, Finset.sum_sub_distrib] using this
  have hnn : ∀ s ∈ Finset.univ, 0 ≤ M.p0 s * (y s - x s) :=
    fun s _ => mul_nonneg (hp0 s).le (by linarith [hxy s])
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hsum (Finset.sum_nonneg hnn))
  intro s
  have := hz s (Finset.mem_univ s)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hp0 s).ne'
  · linarith

theorem prop611 (hR : M.IsRRect) (hp0 : ∀ s, 0 < M.p0 s) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) :
    ∀ π ∈ FactorRMDP.ValueIter.Policies S A, ∀ W₁ ∈ M.Wset,
      IsLeast (M.evalValues lam π) (M.R lam π W₁) →
      ∀ W₀ ∈ M.Wset, ∀ s, M.value lam π W₁ s ≤ M.value lam π W₀ s := by
  intro π hπ W₁ hW₁ hl W₀ hW₀ s
  obtain ⟨W, hW, hmin⟩ := exists_pointwise_min M hR hπ hlam0.le hlam1
  have hR1 : M.R lam π W₁ ≤ M.R lam π W := hl.2 ⟨W, hW, rfl⟩
  have heq := eq_of_R_le M hp0 (hmin W₁ hW₁) hR1
  rw [heq s]
  exact hmin W₀ hW₀ s

end P61Aux

theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    [Nonempty A] {r : ℕ} (M : FactorRMDP.Blackwell.Model S A r) (hR : M.IsRRect) (hp0 : ∀ s, 0 < M.p0 s)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ∀ π ∈ FactorRMDP.ValueIter.Policies S A, ∀ W₁ ∈ M.Wset, IsLeast (M.evalValues lam π) (M.R lam π W₁) →
      ∀ W₀ ∈ M.Wset, ∀ s, M.value lam π W₁ s ≤ M.value lam π W₀ s :=
  P61Aux.prop611 M hR hp0 hlam0 hlam1
