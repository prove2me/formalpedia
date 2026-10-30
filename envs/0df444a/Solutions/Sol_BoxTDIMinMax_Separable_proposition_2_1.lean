-- Prove2me | solution 1 for BoxTDIMinMax.Separable.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:18:21.567791+00:00
-- url     : https://prove2.me/submissions/89d8cd4b-99ef-4607-b4f7-30e12b629a93

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting
import Theorems.Thm_LP_strong_duality_matrix
import Theorems.Thm_LP_farkas

open Matrix BoxTDIMinMax.Separable

namespace BoxTDIMinMax.Separable.Prop21Aux

theorem feas_iff {κ S : Type*} [Fintype κ] (M : Matrix κ S ℚ) (c : S → ℤ) (y : κ → ℝ) :
    y ∈ DualFeas M c ↔ (∀ r, 0 ≤ y r) ∧ ∀ s, ∑ r, y r * (M r s : ℝ) = (c s : ℝ) := by
  unfold DualFeas
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun r => h0 r, fun s => ?_⟩
    have := congrFun h1 s
    simpa [vecMul, dotProduct] using this
  · rintro ⟨h0, h1⟩
    refine ⟨fun r => h0 r, ?_⟩
    funext s
    simpa [vecMul, dotProduct] using h1 s

/-- `y M = c` turns `c x` into `∑_r y_r (M x)_r`. -/
theorem cx_eq {κ S : Type*} [Fintype κ] [Fintype S] (M : Matrix κ S ℚ) (c : S → ℤ)
    (y : κ → ℝ) (hy : ∀ s, ∑ r, y r * (M r s : ℝ) = (c s : ℝ)) (x : S → ℝ) :
    ∑ s, (c s : ℝ) * x s = ∑ r, y r * ∑ s, (M r s : ℝ) * x s := by
  simp_rw [← hy, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem neg_sum {κ : Type*} [Fintype κ] (u : κ → ℝ) : ∑ r, -u r = -∑ r, u r :=
  Finset.sum_neg_distrib _

end BoxTDIMinMax.Separable.Prop21Aux

open BoxTDIMinMax.Separable.Prop21Aux in
theorem solution {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (A : Matrix ι S ℚ) (b : ι → ℚ) (h : IsBoxTDI A b) :
    IsTDI A b := by
  intro c hfe hbdd
  obtain ⟨y0, hy0⟩ := hfe
  obtain ⟨hy00, hy0A⟩ := (feas_iff A c y0).mp hy0
  -- Step 1: the primal system `A x ≥ b` is feasible (Farkas)
  have hprim : ∃ x : S → ℝ, ∀ i, (b i : ℝ) ≤ ∑ s, (A i s : ℝ) * x s := by
    by_contra hnf
    let AR : Matrix ι S ℝ := Matrix.of fun i s => (A i s : ℝ)
    let a : ι → Module.Dual ℝ (S → ℝ) := fun i =>
      -(LinearMap.proj i ∘ₗ Matrix.mulVecLin AR)
    have ha : ∀ i x, a i x = -∑ s, (A i s : ℝ) * x s := by
      intro i x
      simp [a, AR, Matrix.mulVecLin_apply, mulVec, dotProduct]
    have hinf : ¬ ∃ x : S → ℝ, (∀ i, a i x ≤ -(b i : ℝ)) ∧
        ∀ j : Empty, (Empty.elim j : Module.Dual ℝ (S → ℝ)) x = (Empty.elim j : ℝ) := by
      rintro ⟨x, hx, -⟩
      exact hnf ⟨x, fun i => by have := hx i; rw [ha] at this; linarith⟩
    obtain ⟨y, z, hy, hsum, hneg⟩ := (LP.farkas a (fun i => -(b i : ℝ))
      (fun j : Empty => Empty.elim j) (fun j : Empty => Empty.elim j)).mp hinf
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hsum
    have hdz : z ⬝ᵥ (fun j : Empty => (Empty.elim j : ℝ)) = 0 := by
      simp [dotProduct]
    rw [hdz, add_zero] at hneg
    have hyb : 0 < ∑ i, y i * (b i : ℝ) := by
      simp only [dotProduct] at hneg
      have : ∑ i, y i * -(b i : ℝ) = -∑ i, y i * (b i : ℝ) := by
        rw [← neg_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      linarith
    have hyA : ∀ s, ∑ i, y i * (A i s : ℝ) = 0 := by
      intro s
      have h1 := LinearMap.congr_fun hsum (Pi.single s 1)
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.zero_apply, ha] at h1
      have e : ∀ i, ∑ t, (A i t : ℝ) * (Pi.single s (1 : ℝ) : S → ℝ) t = (A i s : ℝ) := by
        intro i
        rw [Finset.sum_eq_single s]
        · simp
        · intro t _ hts; simp [Pi.single_apply, hts]
        · simp
      simp only [e] at h1
      have : ∑ i, y i * (A i s : ℝ) = -∑ i, y i * -(A i s : ℝ) := by
        rw [← neg_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      linarith
    obtain ⟨B, hB⟩ := hbdd
    set t : ℝ := (|B - dualObj b y0| + 1) / ∑ i, y i * (b i : ℝ)
    have ht : 0 ≤ t := div_nonneg (by positivity) hyb.le
    have hfeas : (fun i => y0 i + t * y i) ∈ DualFeas A c := by
      refine (feas_iff A c _).mpr ⟨fun i => ?_, fun s => ?_⟩
      · have := hy00 i; have := hy i
        simp only [Pi.zero_apply] at *
        positivity
      · rw [← hy0A s]
        simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        rw [hyA s]
        ring
    have hval := hB ⟨_, hfeas, rfl⟩
    have hobj : dualObj b (fun i => y0 i + t * y i) =
        dualObj b y0 + t * ∑ i, y i * (b i : ℝ) := by
      unfold dualObj
      simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [hobj] at hval
    have : t * ∑ i, y i * (b i : ℝ) = |B - dualObj b y0| + 1 := by
      simp only [t]; field_simp
    rw [this] at hval
    linarith [le_abs_self (B - dualObj b y0)]
  -- Step 2: strong duality gives an optimal primal `x*` and dual `y*` of equal value
  obtain ⟨xs, ys, hxs, hys0, hysA, hval, -⟩ := LP.strong_duality_matrix
    (Matrix.of fun i s => -(A i s : ℝ))
    (fun i => -(b i : ℝ)) (fun s => -(c s : ℝ))
    (let ⟨x, hx⟩ := hprim; ⟨x, fun i => by
      have := hx i
      simp only [mulVec, dotProduct, Matrix.of_apply, neg_mul, neg_sum]
      linarith⟩)
    ⟨y0, hy00, by
      funext s
      simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, neg_mul, neg_sum,
        neg_inj]
      rw [← hy0A s]; exact Finset.sum_congr rfl (fun _ _ => by ring)⟩
  have hxs' : ∀ i, (b i : ℝ) ≤ ∑ s, (A i s : ℝ) * xs s := by
    intro i
    have := hxs i
    simp only [mulVec, dotProduct, Matrix.of_apply, neg_mul, neg_sum] at this
    linarith
  have hysA' : ∀ s, ∑ i, ys i * (A i s : ℝ) = (c s : ℝ) := by
    intro s
    have := congrFun hysA s
    simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, neg_mul, neg_sum,
      neg_inj] at this
    rw [← this]; exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hval' : ∑ s, (c s : ℝ) * xs s = dualObj b ys := by
    unfold dualObj
    simp only [dotProduct, neg_mul, neg_sum, neg_inj] at hval
    rw [hval]; exact Finset.sum_congr rfl (fun _ _ => by ring)
  -- Step 3: a rational box around `x*` with slack at least one
  set f : S → ℚ := fun s => ((⌊xs s⌋ - 1 : ℤ) : ℚ)
  set g : S → ℚ := fun s => ((⌈xs s⌉ + 1 : ℤ) : ℚ)
  have hf : ∀ s, (f s : ℝ) + 1 ≤ xs s := by
    intro s; simp only [f]; push_cast; linarith [Int.floor_le (xs s)]
  have hg : ∀ s, xs s + 1 ≤ (g s : ℝ) := by
    intro s; simp only [g]; push_cast; linarith [Int.le_ceil (xs s)]
  have hfg : f ≤ g := by
    intro s
    have h1 := hf s; have h2 := hg s
    have : (f s : ℝ) ≤ (g s : ℝ) := by linarith
    exact_mod_cast this
  have hT := h f g hfg
  -- row values of the box matrix at `x*`
  have hrow : ∀ r, ∑ s, ((boxMat A r s : ℚ) : ℝ) * xs s =
      match r with
      | Sum.inl i => ∑ s, (A i s : ℝ) * xs s
      | Sum.inr (Sum.inl t) => xs t
      | Sum.inr (Sum.inr t) => -xs t := by
    intro r
    rcases r with i | t | t
    · simp [boxMat]
    · simp [boxMat, Matrix.one_apply, apply_ite, ite_mul]
    · simp [boxMat, Matrix.one_apply, apply_ite, ite_mul]
  let ind : ι ⊕ (S ⊕ S) → ℝ := fun r => match r with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  have hind : ∀ r, 0 ≤ ind r := by intro r; rcases r with _ | _ <;> simp [ind]
  have hslack : ∀ r, ((boxRhs b f g r : ℚ) : ℝ) + ind r ≤
      ∑ s, ((boxMat A r s : ℚ) : ℝ) * xs s := by
    intro r
    rw [hrow r]
    rcases r with i | t | t
    · simp only [boxRhs, Sum.elim_inl, ind, add_zero]; exact hxs' i
    · simp only [boxRhs, Sum.elim_inr, Sum.elim_inl, ind]; exact hf t
    · simp only [boxRhs, Sum.elim_inr, Pi.neg_apply, Rat.cast_neg, ind]
      linarith [hg t]
  -- the extended dual solution `(y*, 0, 0)`
  set Ys : ι ⊕ (S ⊕ S) → ℝ := Sum.elim ys 0
  have hYsF : Ys ∈ DualFeas (boxMat A) c := by
    refine (feas_iff _ c Ys).mpr ⟨fun r => ?_, fun s => ?_⟩
    · rcases r with i | t
      · exact hys0 i
      · simp [Ys]
    · rw [← hysA' s]
      simp [Fintype.sum_sum_type, Ys, boxMat]
  have hYsObj : dualObj (boxRhs b f g) Ys = dualObj b ys := by
    unfold dualObj
    simp [Fintype.sum_sum_type, Ys, boxRhs]
  have hwk : ∀ Y ∈ DualFeas (boxMat A) c,
      dualObj (boxRhs b f g) Y + ∑ r, Y r * ind r ≤ ∑ s, (c s : ℝ) * xs s := by
    intro Y hY
    obtain ⟨hY0, hYA⟩ := (feas_iff _ c Y).mp hY
    rw [cx_eq (boxMat A) c Y hYA xs]
    unfold dualObj
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun r _ => ?_)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hslack r) (hY0 r)
  have hbdd1 : BddAbove (dualObj (boxRhs b f g) '' DualFeas (boxMat A) c) := by
    refine ⟨∑ s, (c s : ℝ) * xs s, ?_⟩
    rintro _ ⟨Y, hY, rfl⟩
    have h1 := hwk Y hY
    have h2 : 0 ≤ ∑ r, Y r * ind r :=
      Finset.sum_nonneg (fun r _ => mul_nonneg (((feas_iff _ c Y).mp hY).1 r) (hind r))
    linarith
  obtain ⟨Y, hYF, hYopt⟩ := hT c ⟨Ys, hYsF⟩ hbdd1
  obtain ⟨hYF0, hYFA⟩ := (feas_iff _ c _).mp hYF
  -- complementary slackness: the box multipliers vanish
  have hYind : ∑ r, (Y r : ℝ) * ind r = 0 := by
    have h1 := hwk _ hYF
    have h2 := hYopt Ys hYsF
    rw [hYsObj, ← hval'] at h2
    have h3 : 0 ≤ ∑ r, (Y r : ℝ) * ind r :=
      Finset.sum_nonneg (fun r _ => mul_nonneg (hYF0 r) (hind r))
    linarith
  have hY0 : ∀ t, (Y (Sum.inr t) : ℝ) = 0 := by
    intro t
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => mul_nonneg (hYF0 r)
      (hind r))).mp hYind (Sum.inr t) (Finset.mem_univ _)
    simpa [ind] using this
  refine ⟨fun i => Y (Sum.inl i), (feas_iff A c _).mpr ⟨fun i => hYF0 (Sum.inl i),
    fun s => ?_⟩, fun y' hy' => ?_⟩
  · have := hYFA s
    simp only [Fintype.sum_sum_type, hY0, zero_mul, Finset.sum_const_zero, add_zero] at this
    rw [← this]
    simp [boxMat]
  · have hobjY : dualObj (boxRhs b f g) (fun r => (Y r : ℝ)) =
        dualObj b (fun i => (Y (Sum.inl i) : ℝ)) := by
      unfold dualObj
      simp [Fintype.sum_sum_type, hY0, boxRhs]
    rw [← hobjY]
    have h1 := hYopt Ys hYsF
    rw [hYsObj] at h1
    -- weak duality for `A x ≥ b` at `x*`
    obtain ⟨hy'0, hy'A⟩ := (feas_iff A c y').mp hy'
    have h2 : dualObj b y' ≤ ∑ s, (c s : ℝ) * xs s := by
      rw [cx_eq A c y' hy'A xs]
      unfold dualObj
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hxs' i) (hy'0 i))
    linarith
