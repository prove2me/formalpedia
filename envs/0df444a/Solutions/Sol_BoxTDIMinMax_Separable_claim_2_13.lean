-- Prove2me | solution 1 for BoxTDIMinMax.Separable.claim_2_13
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:37:13.845987+00:00
-- url     : https://prove2.me/submissions/935ea25f-ac17-48e0-84ca-9a58d117e278
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting
import Theorems.Thm_LP_strong_duality_matrix
import Theorems.Thm_LP_farkas
import Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_10

open Matrix BoxTDIMinMax.Separable

namespace BoxTDIMinMax.Separable.Claim213Aux

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

theorem cx_eq {κ S : Type*} [Fintype κ] [Fintype S] (M : Matrix κ S ℚ) (c : S → ℤ)
    (y : κ → ℝ) (hy : ∀ s, ∑ r, y r * (M r s : ℝ) = (c s : ℝ)) (x : S → ℝ) :
    ∑ s, (c s : ℝ) * x s = ∑ r, y r * ∑ s, (M r s : ℝ) * x s := by
  simp_rw [← hy, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

/-- The primal feasible set `{x : M x ≥ r}`, written with sums. -/
def Feas {κ S : Type*} [Fintype S] (M : Matrix κ S ℚ) (r : κ → ℚ) (x : S → ℝ) : Prop :=
  ∀ k, (r k : ℝ) ≤ ∑ s, (M k s : ℝ) * x s

/-- Weak duality. -/
theorem weak {κ S : Type*} [Fintype κ] [Fintype S] (M : Matrix κ S ℚ) (r : κ → ℚ) (c : S → ℤ)
    (y : κ → ℝ) (hy : y ∈ DualFeas M c) (x : S → ℝ) (hx : Feas M r x) :
    dualObj r y ≤ ∑ s, (c s : ℝ) * x s := by
  obtain ⟨h0, h1⟩ := (feas_iff M c y).mp hy
  rw [cx_eq M c y h1 x]
  unfold dualObj
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hx k) (h0 k))

/-- A feasible dual with bounded objective forces a feasible primal (Farkas). -/
theorem primal_feas {κ S : Type*} [Fintype κ] [Fintype S] (M : Matrix κ S ℚ) (r : κ → ℚ)
    (c : S → ℤ) (hfe : (DualFeas M c).Nonempty) (hbdd : BddAbove (dualObj r '' DualFeas M c)) :
    ∃ x, Feas M r x := by
  classical
  obtain ⟨y0, hy0⟩ := hfe
  obtain ⟨hy00, hy0A⟩ := (feas_iff M c y0).mp hy0
  by_contra hnf
  let MR : Matrix κ S ℝ := Matrix.of fun i s => (M i s : ℝ)
  let a : κ → Module.Dual ℝ (S → ℝ) := fun i =>
    -(LinearMap.proj i ∘ₗ Matrix.mulVecLin MR)
  have ha : ∀ i x, a i x = -∑ s, (M i s : ℝ) * x s := by
    intro i x
    simp [a, MR, Matrix.mulVecLin_apply, mulVec, dotProduct]
  have hinf : ¬ ∃ x : S → ℝ, (∀ i, a i x ≤ -(r i : ℝ)) ∧
      ∀ j : Empty, (Empty.elim j : Module.Dual ℝ (S → ℝ)) x = (Empty.elim j : ℝ) := by
    rintro ⟨x, hx, -⟩
    exact hnf ⟨x, fun i => by have := hx i; rw [ha] at this; linarith⟩
  obtain ⟨y, z, hy, hsum, hneg⟩ := (LP.farkas a (fun i => -(r i : ℝ))
    (fun j : Empty => Empty.elim j) (fun j : Empty => Empty.elim j)).mp hinf
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hsum
  have hdz : z ⬝ᵥ (fun j : Empty => (Empty.elim j : ℝ)) = 0 := by
    simp [dotProduct]
  rw [hdz, add_zero] at hneg
  have hyb : 0 < ∑ i, y i * (r i : ℝ) := by
    simp only [dotProduct] at hneg
    have : ∑ i, y i * -(r i : ℝ) = -∑ i, y i * (r i : ℝ) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith
  have hyA : ∀ s, ∑ i, y i * (M i s : ℝ) = 0 := by
    intro s
    have h1 := LinearMap.congr_fun hsum (Pi.single s 1)
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply, ha] at h1
    have e : ∀ i, ∑ t, (M i t : ℝ) * (Pi.single s (1 : ℝ) : S → ℝ) t = (M i s : ℝ) := by
      intro i
      rw [Finset.sum_eq_single s]
      · simp
      · intro t _ hts; simp [Pi.single_apply, hts]
      · simp
    simp only [e] at h1
    have : ∑ i, y i * (M i s : ℝ) = -∑ i, y i * -(M i s : ℝ) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith
  obtain ⟨B, hB⟩ := hbdd
  set t : ℝ := (|B - dualObj r y0| + 1) / ∑ i, y i * (r i : ℝ)
  have ht : 0 ≤ t := div_nonneg (by positivity) hyb.le
  have hfeas : (fun i => y0 i + t * y i) ∈ DualFeas M c := by
    refine (feas_iff M c _).mpr ⟨fun i => ?_, fun s => ?_⟩
    · have := hy00 i; have := hy i
      simp only [Pi.zero_apply] at *
      positivity
    · rw [← hy0A s]
      simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      rw [hyA s]
      ring
  have hval := hB ⟨_, hfeas, rfl⟩
  have hobj : dualObj r (fun i => y0 i + t * y i) =
      dualObj r y0 + t * ∑ i, y i * (r i : ℝ) := by
    unfold dualObj
    simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [hobj] at hval
  have : t * ∑ i, y i * (r i : ℝ) = |B - dualObj r y0| + 1 := by
    simp only [t]; field_simp
  rw [this] at hval
  linarith [le_abs_self (B - dualObj r y0)]

/-- Strong duality in the form `min {c x : M x ≥ r} = max {y r : y ≥ 0, y M = c}`. -/
theorem strong {κ S : Type*} [Fintype κ] [Fintype S] (M : Matrix κ S ℚ) (r : κ → ℚ)
    (c : S → ℤ) (hP : ∃ x, Feas M r x) (hD : (DualFeas M c).Nonempty) :
    ∃ x y, Feas M r x ∧ y ∈ DualFeas M c ∧ ∑ s, (c s : ℝ) * x s = dualObj r y ∧
      ∀ x', Feas M r x' → ∑ s, (c s : ℝ) * x s ≤ ∑ s, (c s : ℝ) * x' s := by
  obtain ⟨y0, hy0⟩ := hD
  obtain ⟨hy00, hy0A⟩ := (feas_iff M c y0).mp hy0
  obtain ⟨xs, ys, hxs, hys0, hysA, hval, hopt⟩ := LP.strong_duality_matrix
    (Matrix.of fun i s => -(M i s : ℝ))
    (fun i => -(r i : ℝ)) (fun s => -(c s : ℝ))
    (let ⟨x, hx⟩ := hP; ⟨x, fun i => by
      have := hx i
      simp only [mulVec, dotProduct, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib]
      linarith⟩)
    ⟨y0, hy00, by
      funext s
      simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, neg_mul,
        Finset.sum_neg_distrib, neg_inj]
      rw [← hy0A s]; exact Finset.sum_congr rfl (fun _ _ => by ring)⟩
  have conv : ∀ x, Feas M r x ↔ (Matrix.of fun i s => -(M i s : ℝ)) *ᵥ x ≤
      fun i => -(r i : ℝ) := by
    intro x
    constructor
    · intro hx i
      have := hx i
      simp only [mulVec, dotProduct, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib]
      linarith
    · intro hx i
      have := hx i
      simp only [mulVec, dotProduct, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib] at this
      linarith
  refine ⟨xs, ys, (conv xs).mpr hxs, (feas_iff M c ys).mpr ⟨fun i => hys0 i, fun s => ?_⟩,
    ?_, fun x' hx' => ?_⟩
  · have := congrFun hysA s
    simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, neg_mul,
      Finset.sum_neg_distrib, neg_inj] at this
    rw [← this]; exact Finset.sum_congr rfl (fun _ _ => by ring)
  · unfold dualObj
    simp only [dotProduct, neg_mul, Finset.sum_neg_distrib, neg_inj] at hval
    rw [hval]; exact Finset.sum_congr rfl (fun _ _ => by ring)
  · have := hopt x' ((conv x').mp hx')
    simp only [dotProduct, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] at this
    exact this

/-- An optimal primal solution forces a feasible dual (Farkas). -/
theorem dual_feas {κ S : Type*} [Fintype κ] [Fintype S] [DecidableEq S] (M : Matrix κ S ℚ)
    (r : κ → ℚ) (c : S → ℤ) (x0 : S → ℝ) (hx0 : Feas M r x0)
    (hopt : ∀ x, Feas M r x → ∑ s, (c s : ℝ) * x0 s ≤ ∑ s, (c s : ℝ) * x s) :
    (DualFeas M c).Nonempty := by
  classical
  by_contra hnf
  let a : κ → Module.Dual ℝ (κ → ℝ) := fun k => -LinearMap.proj k
  let e : S → Module.Dual ℝ (κ → ℝ) := fun s =>
    ∑ k, (M k s : ℝ) • LinearMap.proj k
  have he : ∀ s y, e s y = ∑ k, y k * (M k s : ℝ) := by
    intro s y
    simp [e, mul_comm]
  have hinf : ¬ ∃ y : κ → ℝ, (∀ k, a k y ≤ (0 : κ → ℝ) k) ∧ ∀ s, e s y = (c s : ℝ) := by
    rintro ⟨y, hy, hyc⟩
    apply hnf
    refine ⟨y, (feas_iff M c y).mpr ⟨fun k => ?_, fun s => ?_⟩⟩
    · have := hy k; simp [a] at this; exact this
    · rw [← hyc s, he]
  obtain ⟨w, z, hw, hsum, hneg⟩ := (LP.farkas a (0 : κ → ℝ) e (fun s => (c s : ℝ))).mp hinf
  -- `M z = w ≥ 0` and `c z < 0`
  have hMz : ∀ k, 0 ≤ ∑ s, (M k s : ℝ) * z s := by
    intro k
    have h1 := LinearMap.congr_fun hsum (Pi.single k 1)
    simp only [LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, LinearMap.zero_apply, he, a, LinearMap.neg_apply, LinearMap.proj_apply] at h1
    have e1 : ∀ s, ∑ j, (Pi.single k (1 : ℝ) : κ → ℝ) j * (M j s : ℝ) = (M k s : ℝ) := by
      intro s
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; simp [Pi.single_apply, hjk]
      · simp
    simp only [e1] at h1
    have e2 : ∑ j, w j * -(Pi.single k (1 : ℝ) : κ → ℝ) j = -w k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; simp [Pi.single_apply, hjk]
      · simp
    rw [e2] at h1
    have := hw k
    simp only [Pi.zero_apply] at this
    have h3 : ∑ s, (M k s : ℝ) * z s = ∑ s, z s * (M k s : ℝ) :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    linarith
  have hcz : ∑ s, (c s : ℝ) * z s < 0 := by
    simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at hneg
    have : ∑ s, (c s : ℝ) * z s = ∑ s, z s * (c s : ℝ) :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    linarith
  have hx1 : Feas M r (x0 + z) := by
    intro k
    have h1 := hx0 k
    have h2 := hMz k
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    linarith
  have := hopt _ hx1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at this
  linarith


/-- A primal objective bounded below on a nonempty polyhedron forces a feasible dual. -/
theorem dual_feas_bdd {κ S : Type*} [Fintype κ] [Fintype S] [DecidableEq S]
    (M : Matrix κ S ℚ) (r : κ → ℚ) (c : S → ℤ) (x0 : S → ℝ) (hx0 : Feas M r x0)
    (hbdd : ∃ B : ℝ, ∀ x, Feas M r x → B ≤ ∑ s, (c s : ℝ) * x s) :
    (DualFeas M c).Nonempty := by
  obtain ⟨B, hB⟩ := hbdd
  -- first get an optimal point: otherwise use the unbounded direction from Farkas
  by_contra hnf
  have key : ∃ z : S → ℝ, (∀ k, 0 ≤ ∑ s, (M k s : ℝ) * z s) ∧ ∑ s, (c s : ℝ) * z s < 0 := by
    classical
    let a : κ → Module.Dual ℝ (κ → ℝ) := fun k => -LinearMap.proj k
    let e : S → Module.Dual ℝ (κ → ℝ) := fun s =>
      ∑ k, (M k s : ℝ) • LinearMap.proj k
    have he : ∀ s y, e s y = ∑ k, y k * (M k s : ℝ) := by
      intro s y
      simp [e, mul_comm]
    have hinf : ¬ ∃ y : κ → ℝ, (∀ k, a k y ≤ (0 : κ → ℝ) k) ∧ ∀ s, e s y = (c s : ℝ) := by
      rintro ⟨y, hy, hyc⟩
      apply hnf
      refine ⟨y, (feas_iff M c y).mpr ⟨fun k => ?_, fun s => ?_⟩⟩
      · have := hy k; simp [a] at this; exact this
      · rw [← hyc s, he]
    obtain ⟨w, z, hw, hsum, hneg⟩ := (LP.farkas a (0 : κ → ℝ) e (fun s => (c s : ℝ))).mp hinf
    refine ⟨z, fun k => ?_, ?_⟩
    · have h1 := LinearMap.congr_fun hsum (Pi.single k 1)
      simp only [LinearMap.add_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, LinearMap.zero_apply, he, a, LinearMap.neg_apply, LinearMap.proj_apply] at h1
      have e1 : ∀ s, ∑ j, (Pi.single k (1 : ℝ) : κ → ℝ) j * (M j s : ℝ) = (M k s : ℝ) := by
        intro s
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hjk; simp [Pi.single_apply, hjk]
        · simp
      simp only [e1] at h1
      have e2 : ∑ j, w j * -(Pi.single k (1 : ℝ) : κ → ℝ) j = -w k := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hjk; simp [Pi.single_apply, hjk]
        · simp
      rw [e2] at h1
      have := hw k
      simp only [Pi.zero_apply] at this
      have h3 : ∑ s, (M k s : ℝ) * z s = ∑ s, z s * (M k s : ℝ) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      linarith
    · simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at hneg
      have : ∑ s, (c s : ℝ) * z s = ∑ s, z s * (c s : ℝ) :=
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
      linarith
  obtain ⟨z, hMz, hcz⟩ := key
  set t : ℝ := (|∑ s, (c s : ℝ) * x0 s - B| + 1) / (-∑ s, (c s : ℝ) * z s)
  have ht : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  have hx1 : Feas M r (fun s => x0 s + t * z s) := by
    intro k
    have h1 := hx0 k
    have h2 := mul_nonneg ht (hMz k)
    simp only [mul_add, Finset.sum_add_distrib]
    have : ∑ s, (M k s : ℝ) * (t * z s) = t * ∑ s, (M k s : ℝ) * z s := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    linarith
  have h := hB _ hx1
  have e : ∑ s, (c s : ℝ) * (x0 s + t * z s) =
      ∑ s, (c s : ℝ) * x0 s + t * ∑ s, (c s : ℝ) * z s := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1; exact Finset.sum_congr rfl (fun _ _ => by ring)
  have e2 : t * ∑ s, (c s : ℝ) * z s = -(|∑ s, (c s : ℝ) * x0 s - B| + 1) := by
    have hne : (-∑ s, (c s : ℝ) * z s) ≠ 0 := by linarith
    simp only [t]
    rw [div_mul_eq_mul_div, div_eq_iff hne]
    ring
  rw [e, e2] at h
  linarith [le_abs_self (∑ s, (c s : ℝ) * x0 s - B)]

/-- On a nonempty polyhedron on which every integral objective is bounded below, every
integral objective attains its minimum. -/
theorem exists_opt {κ S : Type*} [Fintype κ] [Fintype S] [DecidableEq S]
    (M : Matrix κ S ℚ) (r : κ → ℚ) (c : S → ℤ) (hne : ∃ x, Feas M r x)
    (hbdd : ∃ B : ℝ, ∀ x, Feas M r x → B ≤ ∑ s, (c s : ℝ) * x s) :
    ∃ x, Feas M r x ∧ ∀ x', Feas M r x' → ∑ s, (c s : ℝ) * x s ≤ ∑ s, (c s : ℝ) * x' s := by
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨x, -, hx, -, -, hopt⟩ := strong M r c ⟨x0, hx0⟩ (dual_feas_bdd M r c x0 hx0 hbdd)
  exact ⟨x, hx, hopt⟩

/-- TDI with integral right-hand side: every integral objective has an integral optimal value. -/
theorem tdi_int_val {κ S : Type*} [Fintype κ] [Fintype S] [DecidableEq S]
    (M : Matrix κ S ℚ) (r : κ → ℚ) (hr : ∀ k, ∃ n : ℤ, r k = n) (hT : IsTDI M r)
    (c : S → ℤ) (x : S → ℝ) (hx : Feas M r x)
    (hopt : ∀ x', Feas M r x' → ∑ s, (c s : ℝ) * x s ≤ ∑ s, (c s : ℝ) * x' s) :
    ∃ k : ℤ, ∑ s, (c s : ℝ) * x s = k := by
  have hfe := dual_feas M r c x hx hopt
  have hbdd : BddAbove (dualObj r '' DualFeas M c) := by
    refine ⟨∑ s, (c s : ℝ) * x s, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact weak M r c y hy x hx
  obtain ⟨y, hyF, hyopt⟩ := hT c hfe hbdd
  obtain ⟨x2, y2, hx2, hy2, hval2, hopt2⟩ := strong M r c ⟨x, hx⟩ hfe
  have heq : ∑ s, (c s : ℝ) * x2 s = ∑ s, (c s : ℝ) * x s :=
    le_antisymm (hopt2 x hx) (hopt x2 hx2)
  have h1 : ∑ s, (c s : ℝ) * x s ≤ dualObj r (fun k => (y k : ℝ)) := by
    rw [← heq, hval2]; exact hyopt y2 hy2
  have h2 := weak M r c _ hyF x hx
  choose n hn using hr
  refine ⟨∑ k, y k * n k, ?_⟩
  have : dualObj r (fun k => (y k : ℝ)) = ((∑ k, y k * n k : ℤ) : ℝ) := by
    unfold dualObj; push_cast; simp only [hn]; push_cast; rfl
  linarith

universe u in
/-- Integral optimal points (Hoffman / Edmonds–Giles): on a nonempty polyhedron on which every
integral objective is bounded below and has an integral optimal value, every integral objective
has an optimal point whose coordinates in `T` are integers. -/
theorem int_opt {S : Type*} [Fintype S] [DecidableEq S] (T : Finset S) :
    ∀ {κ : Type u} [Fintype κ] (M : Matrix κ S ℚ) (r : κ → ℚ), (∃ x, Feas M r x) →
    (∀ c : S → ℤ, ∃ B : ℝ, ∀ x, Feas M r x → B ≤ ∑ s, (c s : ℝ) * x s) →
    (∀ c : S → ℤ, ∀ x, Feas M r x →
      (∀ x', Feas M r x' → ∑ s, (c s : ℝ) * x s ≤ ∑ s, (c s : ℝ) * x' s) →
      ∃ k : ℤ, ∑ s, (c s : ℝ) * x s = k) →
    ∀ c : S → ℤ, ∃ x, Feas M r x ∧
      (∀ x', Feas M r x' → ∑ s, (c s : ℝ) * x s ≤ ∑ s, (c s : ℝ) * x' s) ∧
      ∀ j ∈ T, ∃ k : ℤ, x j = k := by
  induction T using Finset.induction_on with
  | empty =>
    intro κ _ M r hne hbdd _ c
    obtain ⟨x, hx, hopt⟩ := exists_opt M r c hne (hbdd c)
    exact ⟨x, hx, hopt, by simp⟩
  | insert j T hj ih =>
    intro κ _ M r hne hbdd hint c
    obtain ⟨x0, hx0, hopt0⟩ := exists_opt M r c hne (hbdd c)
    obtain ⟨k0, hk0⟩ := hint c x0 hx0 hopt0
    let M' : Matrix (κ ⊕ PUnit.{u+1}) S ℚ :=
      Matrix.fromRows M (Matrix.of fun _ s => -(c s : ℚ))
    let r' : κ ⊕ PUnit.{u+1} → ℚ := Sum.elim r (fun _ => -(k0 : ℚ))
    have hF : ∀ x, Feas M' r' x ↔ Feas M r x ∧ ∑ s, (c s : ℝ) * x s ≤ k0 := by
      intro x
      constructor
      · intro hx
        refine ⟨fun k => by simpa [M', r'] using hx (Sum.inl k), ?_⟩
        have := hx (Sum.inr PUnit.unit)
        simp only [M', r', Matrix.fromRows_apply_inr, Matrix.of_apply, Sum.elim_inr,
          Rat.cast_neg, Rat.cast_intCast, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]
          at this
        exact this
      · rintro ⟨hx, hc⟩ k
        rcases k with k | u
        · simpa [M', r'] using hx k
        · simp only [M', r', Matrix.fromRows_apply_inr, Matrix.of_apply, Sum.elim_inr,
            Rat.cast_neg, Rat.cast_intCast, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff]
          exact hc
    have hFopt : ∀ x, Feas M' r' x → ∀ x', Feas M r x' →
        ∑ s, (c s : ℝ) * x s ≤ ∑ s, (c s : ℝ) * x' s := by
      intro x hx x' hx'
      have h1 := ((hF x).mp hx).2
      have h2 := hopt0 x' hx'
      rw [hk0] at h2
      linarith
    have hne' : ∃ x, Feas M' r' x := ⟨x0, (hF x0).mpr ⟨hx0, hk0.le⟩⟩
    have hbdd' : ∀ c' : S → ℤ, ∃ B : ℝ, ∀ x, Feas M' r' x → B ≤ ∑ s, (c' s : ℝ) * x s :=
      fun c' => let ⟨B, hB⟩ := hbdd c'; ⟨B, fun x hx => hB x ((hF x).mp hx).1⟩
    have hint' : ∀ c' : S → ℤ, ∀ x', Feas M' r' x' →
        (∀ x'', Feas M' r' x'' → ∑ s, (c' s : ℝ) * x' s ≤ ∑ s, (c' s : ℝ) * x'' s) →
        ∃ k : ℤ, ∑ s, (c' s : ℝ) * x' s = k := by
      intro c' x' hx' hopt'
      obtain ⟨hx'P, hx'c⟩ := (hF x').mp hx'
      have hcx' : ∑ s, (c s : ℝ) * x' s = k0 :=
        le_antisymm hx'c (by rw [← hk0]; exact hopt0 x' hx'P)
      obtain ⟨xh, Y, hxh, hY, hvalY, hoptY⟩ :=
        strong M' r' c' ⟨x', hx'⟩ (dual_feas M' r' c' x' hx' hopt')
      have hxh_eq : ∑ s, (c' s : ℝ) * xh s = ∑ s, (c' s : ℝ) * x' s :=
        le_antisymm (hoptY x' hx') (hopt' xh hxh)
      obtain ⟨hY0, hYA⟩ := (feas_iff M' c' Y).mp hY
      set lam := Y (Sum.inr PUnit.unit) with hlam
      have hcol : ∀ s, ∑ k, Y (Sum.inl k) * (M k s : ℝ) - lam * (c s : ℝ) = (c' s : ℝ) := by
        intro s
        have := hYA s
        rw [Fintype.sum_sum_type] at this
        simp only [M', Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.of_apply,
          Rat.cast_neg, Rat.cast_intCast, Finset.univ_unique, Finset.sum_singleton] at this
        rw [← this, hlam]
        simp only [PUnit.default_eq_unit]
        ring
      have hobjY : dualObj r' Y = dualObj r (fun k => Y (Sum.inl k)) - lam * (k0 : ℝ) := by
        unfold dualObj
        rw [Fintype.sum_sum_type]
        simp only [r', Sum.elim_inl, Sum.elim_inr, Rat.cast_neg, Rat.cast_intCast,
          Finset.univ_unique, Finset.sum_singleton, hlam, PUnit.default_eq_unit]
        ring
      obtain ⟨xt, u, hxt, hu, hvalu, hoptu⟩ :=
        strong M r c ⟨x0, hx0⟩ (dual_feas M r c x0 hx0 hopt0)
      have hxt_eq : ∑ s, (c s : ℝ) * xt s = k0 :=
        le_antisymm (by rw [← hk0]; exact hoptu x0 hx0) (by rw [← hk0]; exact hopt0 xt hxt)
      obtain ⟨hu0, huA⟩ := (feas_iff M c u).mp hu
      set K : ℤ := ⌈lam⌉ with hKdef
      have hK : lam ≤ (K : ℝ) := Int.le_ceil lam
      set z : κ → ℝ := fun k => Y (Sum.inl k) + ((K : ℝ) - lam) * u k with hzdef
      have hz0 : ∀ k, 0 ≤ z k := fun k =>
        add_nonneg (hY0 _) (mul_nonneg (by linarith) (hu0 k))
      set c2 : S → ℤ := fun s => c' s + K * c s with hc2
      have hzA : ∀ s, ∑ k, z k * (M k s : ℝ) = (c2 s : ℝ) := by
        intro s
        simp only [hzdef, hc2, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
          huA s]
        push_cast
        linarith [hcol s]
      have hzr : dualObj r z = ∑ s, (c' s : ℝ) * x' s + (K : ℝ) * k0 := by
        unfold dualObj
        simp only [hzdef, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        have h1 : ∑ k, Y (Sum.inl k) * (r k : ℝ) = dualObj r (fun k => Y (Sum.inl k)) := rfl
        have h2 : ∑ k, u k * (r k : ℝ) = dualObj r u := rfl
        rw [h1, h2, ← hvalu, hxt_eq]
        have : dualObj r (fun k => Y (Sum.inl k)) = ∑ s, (c' s : ℝ) * x' s + lam * k0 := by
          rw [← hxh_eq, hvalY, hobjY]; ring
        rw [this]; ring
      have e : ∑ s, (c2 s : ℝ) * x' s = ∑ s, (c' s : ℝ) * x' s + (K : ℝ) * k0 := by
        simp only [hc2]
        push_cast
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hcx']
      have hopt2 : ∀ x, Feas M r x → ∑ s, (c2 s : ℝ) * x' s ≤ ∑ s, (c2 s : ℝ) * x s := by
        intro x hx
        have hw := weak M r c2 z ((feas_iff M c2 z).mpr ⟨hz0, hzA⟩) x hx
        rw [e, ← hzr]; exact hw
      obtain ⟨k1, hk1⟩ := hint c2 x' hx'P hopt2
      refine ⟨k1 - K * k0, ?_⟩
      push_cast
      linarith
    obtain ⟨x, hx, hoptx, hTx⟩ := ih M' r' hne' hbdd' hint' (Pi.single j 1)
    refine ⟨x, ((hF x).mp hx).1, hFopt x hx, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · obtain ⟨k, hk⟩ := hint' (Pi.single i 1) x hx hoptx
      refine ⟨k, ?_⟩
      rw [← hk]
      rw [Finset.sum_eq_single i]
      · simp
      · intro t _ hti; simp [Pi.single_apply, hti]
      · simp
    · exact hTx i hi

section
variable {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
/-- Column sums of the box matrix of the auxiliary system (2.8). -/
theorem colsum (Q : Matrix ι S ℤ) (Y : ((S ⊕ S) ⊕ ι) ⊕ ((S ⊕ S) ⊕ (S ⊕ S)) → ℝ)
    (t : S ⊕ S) :
    ∑ r, Y r * ((boxMat (auxMat Q) r t : ℚ) : ℝ) =
      Y (Sum.inl (Sum.inl t)) +
        ∑ i, Y (Sum.inl (Sum.inr i)) * ((auxMat Q (Sum.inr i) t : ℚ) : ℝ) +
        Y (Sum.inr (Sum.inl t)) - Y (Sum.inr (Sum.inr t)) := by
  simp only [Fintype.sum_sum_type]
  rcases t with s | s <;> simp [boxMat, auxMat, Matrix.one_apply, apply_ite] <;> ring

theorem aux_inl (Q : Matrix ι S ℤ) (i : ι) (s : S) :
    ((auxMat Q (Sum.inr i) (Sum.inl s) : ℚ) : ℝ) = -(Q i s : ℝ) := by
  simp [auxMat, ratMat]

theorem aux_inr (Q : Matrix ι S ℤ) (i : ι) (s : S) :
    ((auxMat Q (Sum.inr i) (Sum.inr s) : ℚ) : ℝ) = (Q i s : ℝ) := by
  simp [auxMat, ratMat]

/-- Row values of the box matrix of (2.8) at a real point `x`. -/
theorem rowval (Q : Matrix ι S ℤ) (x : S ⊕ S → ℝ) :
    (∀ t, ∑ u, ((boxMat (auxMat Q) (Sum.inl (Sum.inl t)) u : ℚ) : ℝ) * x u = x t) ∧
    (∀ i, ∑ u, ((boxMat (auxMat Q) (Sum.inl (Sum.inr i)) u : ℚ) : ℝ) * x u =
      ∑ s, (Q i s : ℝ) * x (Sum.inr s) - ∑ s, (Q i s : ℝ) * x (Sum.inl s)) ∧
    (∀ t, ∑ u, ((boxMat (auxMat Q) (Sum.inr (Sum.inl t)) u : ℚ) : ℝ) * x u = x t) ∧
    (∀ t, ∑ u, ((boxMat (auxMat Q) (Sum.inr (Sum.inr t)) u : ℚ) : ℝ) * x u = -x t) := by
  refine ⟨fun t => ?_, fun i => ?_, fun t => ?_, fun t => ?_⟩
  · simp [boxMat, auxMat, Matrix.one_apply, ite_mul, apply_ite]
  · simp only [Fintype.sum_sum_type]
    simp [boxMat, auxMat, ratMat]
    ring
  · simp [boxMat, Matrix.one_apply, ite_mul, apply_ite]
  · simp [boxMat, Matrix.one_apply, ite_mul, apply_ite]

end

theorem esum {S : Type*} (T : Finset S) (g : S → ℤ) :
    ∑ s ∈ T, (((g s : ℤ) : ℝ) : EReal) = (((∑ s ∈ T, g s : ℤ) : ℝ) : EReal) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, ih]
    push_cast
    rfl


end BoxTDIMinMax.Separable.Claim213Aux


open BoxTDIMinMax.Separable.Claim213Aux in
theorem solution {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (zStar : S → ℤ) (hz : zStar ∈ intPts Q p)
    (lo up : S → EReal)
    (hlo : ∀ s, lo s = ⊥ ∨ ∃ k : ℤ, lo s = ((k : ℝ) : EReal))
    (hup : ∀ s, up s = ⊤ ∨ ∃ k : ℤ, up s = ((k : ℝ) : EReal))
    (hlu : ∀ s, lo s ≤ up s)
    (h29 : Cond29 Q p zStar lo up) :
    IsLeast {v : ℝ | ∃ x₁ x₂ : S → ℝ, 0 ≤ x₁ ∧ 0 ≤ x₂ ∧
        (∀ s, lo s = ⊥ → x₁ s = 0) ∧ (∀ s, up s = ⊤ → x₂ s = 0) ∧
        (∀ i, (((p - Q *ᵥ zStar) i : ℤ) : ℝ) ≤
          ∑ s, (Q i s : ℝ) * x₂ s - ∑ s, (Q i s : ℝ) * x₁ s) ∧
        v = ∑ s, (up s).toReal * x₂ s - ∑ s, (lo s).toReal * x₁ s} 0 := by
  have hpQ : ∀ i, (((p - Q *ᵥ zStar) i : ℤ) : ℝ) ≤ 0 := by
    intro i; have := hz i; simp only [Pi.sub_apply]; push_cast
    have : ((p i : ℤ) : ℝ) ≤ (((Q *ᵥ zStar) i : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  refine ⟨⟨0, 0, le_rfl, le_rfl, fun _ _ => rfl, fun _ _ => rfl, fun i => by simpa using hpQ i,
    by simp⟩, ?_⟩
  rintro _ ⟨x1, x2, h1, h2, hf1, hf2, hQ, rfl⟩
  by_contra hneg
  push_neg at hneg
  -- integer bounds and the cost vector
  set Lz : S → ℤ := fun s => ⌊(lo s).toReal⌋ with hLzdef
  set Uz : S → ℤ := fun s => ⌊(up s).toReal⌋ with hUzdef
  have hLz : ∀ s, (lo s).toReal = (Lz s : ℝ) := by
    intro s; rcases hlo s with h | ⟨k, h⟩ <;> simp [Lz, h]
  have hUz : ∀ s, (up s).toReal = (Uz s : ℝ) := by
    intro s; rcases hup s with h | ⟨k, h⟩ <;> simp [Uz, h]
  have hLz' : ∀ s, lo s ≠ ⊥ → lo s = ((Lz s : ℝ) : EReal) := by
    intro s hs
    rcases hlo s with h | ⟨k, h⟩
    · exact absurd h hs
    · rw [h]; simp [Lz, h]
  have hUz' : ∀ s, up s ≠ ⊤ → up s = ((Uz s : ℝ) : EReal) := by
    intro s hs
    rcases hup s with h | ⟨k, h⟩
    · exact absurd h hs
    · rw [h]; simp [Uz, h]
  set cost : S ⊕ S → ℤ := Sum.elim (fun s => -Lz s) Uz with hcost
  set f : S ⊕ S → ℚ := 0 with hf
  set g : S ⊕ S → ℚ := Sum.elim (fun s => if lo s = ⊥ then 0 else 1)
    (fun s => if up s = ⊤ then 0 else 1) with hg
  have hfg : f ≤ g := by
    intro t
    rcases t with s | s
    · simp only [hf, hg, Pi.zero_apply, Sum.elim_inl]; split_ifs <;> norm_num
    · simp only [hf, hg, Pi.zero_apply, Sum.elim_inr]; split_ifs <;> norm_num
  have hg01 : ∀ t, (g t : ℝ) = 0 ∨ (g t : ℝ) = 1 := by
    intro t
    rcases t with s | s
    · simp only [hg, Sum.elim_inl]; split_ifs <;> simp
    · simp only [hg, Sum.elim_inr]; split_ifs <;> simp
  have hT := proposition_2_10 Q p hbox zStar hz f g hfg
  set B := boxMat (auxMat Q) with hB
  set rhs := boxRhs (auxRhs Q p zStar) f g with hrhs
  have rhs_nn : ∀ t, (rhs (Sum.inl (Sum.inl t)) : ℝ) = 0 := by
    intro t; simp [rhs, boxRhs, auxRhs]
  have rhs_Q : ∀ i, (rhs (Sum.inl (Sum.inr i)) : ℝ) = (((p - Q *ᵥ zStar) i : ℤ) : ℝ) := by
    intro i; simp [rhs, boxRhs, auxRhs, ratVec]
  have rhs_lo : ∀ t, (rhs (Sum.inr (Sum.inl t)) : ℝ) = 0 := by
    intro t; simp [rhs, boxRhs, f]
  have rhs_up : ∀ t, (rhs (Sum.inr (Sum.inr t)) : ℝ) = -(g t : ℝ) := by
    intro t; simp [rhs, boxRhs]
  have hrint : ∀ r, ∃ n : ℤ, rhs r = n := by
    intro r
    rcases r with (t | i) | (t | t)
    · exact ⟨0, by simp [rhs, boxRhs, auxRhs]⟩
    · exact ⟨(p - Q *ᵥ zStar) i, by simp [rhs, boxRhs, auxRhs, ratVec]⟩
    · exact ⟨0, by simp [rhs, boxRhs, f]⟩
    · rcases t with s | s
      · by_cases h : lo s = ⊥
        · exact ⟨0, by simp [rhs, boxRhs, g, h]⟩
        · exact ⟨-1, by simp [rhs, boxRhs, g, h]⟩
      · by_cases h : up s = ⊤
        · exact ⟨0, by simp [rhs, boxRhs, g, h]⟩
        · exact ⟨-1, by simp [rhs, boxRhs, g, h]⟩
  -- the feasible region of the boxed system
  have feasB : ∀ x, Feas B rhs x ↔ (∀ t, 0 ≤ x t) ∧
      (∀ i, (((p - Q *ᵥ zStar) i : ℤ) : ℝ) ≤
        ∑ s, (Q i s : ℝ) * x (Sum.inr s) - ∑ s, (Q i s : ℝ) * x (Sum.inl s)) ∧
      (∀ t, x t ≤ (g t : ℝ)) := by
    intro x
    obtain ⟨rv1, rv2, rv3, rv4⟩ := rowval Q x
    constructor
    · intro hx
      refine ⟨fun t => ?_, fun i => ?_, fun t => ?_⟩
      · have := hx (Sum.inl (Sum.inl t)); rw [rhs_nn, rv1] at this; exact this
      · have := hx (Sum.inl (Sum.inr i)); rw [rhs_Q, rv2] at this; exact this
      · have := hx (Sum.inr (Sum.inr t)); rw [rhs_up, rv4] at this; linarith
    · rintro ⟨hx0, hxQ, hxg⟩ r
      rcases r with (t | i) | (t | t)
      · rw [rhs_nn, rv1]; exact hx0 t
      · rw [rhs_Q, rv2]; exact hxQ i
      · rw [rhs_lo, rv3]; exact hx0 t
      · rw [rhs_up, rv4]; linarith [hxg t]
  have hg1 : ∀ t, (g t : ℝ) ≤ 1 := fun t => by rcases hg01 t with h | h <;> rw [h] <;> norm_num
  have hbdd : ∀ c : S ⊕ S → ℤ, ∃ b : ℝ, ∀ x, Feas B rhs x → b ≤ ∑ t, (c t : ℝ) * x t := by
    intro c
    refine ⟨-∑ t, |(c t : ℝ)|, fun x hx => ?_⟩
    obtain ⟨hx0, -, hxg⟩ := (feasB x).mp hx
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum (fun t _ => ?_)
    have a1 := neg_abs_le (c t : ℝ)
    have a2 := hx0 t
    have a3 : x t ≤ 1 := (hxg t).trans (hg1 t)
    have a4 := abs_nonneg (c t : ℝ)
    nlinarith
  have hne : ∃ x, Feas B rhs x := by
    refine ⟨0, (feasB 0).mpr ⟨fun t => le_rfl, fun i => by simpa using hpQ i, fun t => ?_⟩⟩
    have := hfg t; simp only [hf, Pi.zero_apply] at this
    simp only [Pi.zero_apply]; exact_mod_cast this
  obtain ⟨xs, hxs, hopt, hxint⟩ := int_opt (Finset.univ : Finset (S ⊕ S)) B rhs hne hbdd
    (fun c x hx hopt => tdi_int_val B rhs hrint hT c x hx hopt) cost
  -- the scaled point `ε (x₁, x₂)` is feasible with negative cost
  set x' : S ⊕ S → ℝ := Sum.elim x1 x2 with hx'
  have hx'0 : ∀ t, 0 ≤ x' t := by
    intro t; rcases t with s | s
    · exact h1 s
    · exact h2 s
  set ε : ℝ := 1 / (1 + ∑ t, x' t) with hε
  have hsum0 : 0 ≤ ∑ t, x' t := Finset.sum_nonneg (fun t _ => hx'0 t)
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by rw [hε, div_le_one (by linarith)]; linarith
  have hεx : ∀ t, ε * x' t ≤ 1 := by
    intro t
    have : x' t ≤ ∑ t, x' t := Finset.single_le_sum (fun t _ => hx'0 t) (Finset.mem_univ t)
    rw [hε, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
    linarith
  have hxe : Feas B rhs (fun t => ε * x' t) := by
    refine (feasB _).mpr ⟨fun t => mul_nonneg hε0.le (hx'0 t), fun i => ?_, fun t => ?_⟩
    · have := hQ i
      have e1 : ∑ s, (Q i s : ℝ) * (ε * x' (Sum.inr s)) -
          ∑ s, (Q i s : ℝ) * (ε * x' (Sum.inl s)) =
          ε * (∑ s, (Q i s : ℝ) * x2 s - ∑ s, (Q i s : ℝ) * x1 s) := by
        simp only [hx', Sum.elim_inl, Sum.elim_inr, mul_sub, Finset.mul_sum]
        congr 1 <;> exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e1]
      have := hpQ i
      nlinarith
    · rcases hg01 t with h | h
      · rw [h]
        rcases t with s | s
        · have hs : lo s = ⊥ := by
            by_contra hs; simp [hg, hs] at h
          simp [hx', hf1 s hs]
        · have hs : up s = ⊤ := by
            by_contra hs; simp [hg, hs] at h
          simp [hx', hf2 s hs]
      · rw [h]; exact hεx t
  have hcostx' : ∑ t, (cost t : ℝ) * x' t =
      ∑ s, (up s).toReal * x2 s - ∑ s, (lo s).toReal * x1 s := by
    rw [Fintype.sum_sum_type]
    simp only [hcost, hx', Sum.elim_inl, Sum.elim_inr, hLz, hUz, Int.cast_neg, neg_mul,
      Finset.sum_neg_distrib]
    ring
  have hcost_lt : ∑ t, (cost t : ℝ) * xs t < 0 := by
    have := hopt _ hxe
    have e : ∑ t, (cost t : ℝ) * (ε * x' t) = ε * ∑ t, (cost t : ℝ) * x' t := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [e, hcostx'] at this
    have : ε * (∑ s, (up s).toReal * x2 s - ∑ s, (lo s).toReal * x1 s) < 0 :=
      mul_neg_of_pos_of_neg hε0 hneg
    linarith
  -- the optimal point is {0,1}-valued
  choose xi hxi using fun t => hxint t (Finset.mem_univ t)
  obtain ⟨hxs0, hxsQ, hxsg⟩ := (feasB xs).mp hxs
  have hxi01 : ∀ t, 0 ≤ xi t ∧ xi t ≤ 1 := by
    intro t
    have a := hxs0 t; have b := (hxsg t).trans (hg1 t)
    rw [hxi t] at a b
    exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
  have hfix : ∀ t, xi t = 1 → (g t : ℝ) = 1 := by
    intro t ht
    rcases hg01 t with h | h
    · have := hxsg t; rw [hxi t, ht, h] at this; norm_num at this
    · exact h
  have lo_fin : ∀ s, xi (Sum.inl s) = 1 → lo s ≠ ⊥ := by
    intro s hs hb
    have := hfix _ hs; simp [hg, hb] at this
  have up_fin : ∀ s, xi (Sum.inr s) = 1 → up s ≠ ⊤ := by
    intro s hs hb
    have := hfix _ hs; simp [hg, hb] at this
  set Sp := Finset.univ.filter (fun s => xi (Sum.inr s) = 1 ∧ xi (Sum.inl s) = 0) with hSp
  set Sm := Finset.univ.filter (fun s => xi (Sum.inl s) = 1 ∧ xi (Sum.inr s) = 0) with hSm
  have hdisj : Disjoint Sm Sp := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [hSm, hSp, Finset.mem_filter] at hs hs'
    omega
  have hchi : ∀ s, (chi Sp s : ℤ) - chi Sm s = xi (Sum.inr s) - xi (Sum.inl s) := by
    intro s
    obtain ⟨a0, a1⟩ := hxi01 (Sum.inr s)
    obtain ⟨b0, b1⟩ := hxi01 (Sum.inl s)
    simp only [chi, hSp, hSm, Finset.mem_filter, Finset.mem_univ, true_and]
    interval_cases (xi (Sum.inr s)) <;> interval_cases (xi (Sum.inl s)) <;> simp
  have hz' : zStar + chi Sp - chi Sm ∈ intPts Q p := by
    intro i
    have h := hxsQ i
    simp only [hxi] at h
    have h' : (p - Q *ᵥ zStar) i ≤
        ∑ s, Q i s * xi (Sum.inr s) - ∑ s, Q i s * xi (Sum.inl s) := by exact_mod_cast h
    have e : (Q *ᵥ (zStar + chi Sp - chi Sm)) i =
        (Q *ᵥ zStar) i + (∑ s, Q i s * xi (Sum.inr s) - ∑ s, Q i s * xi (Sum.inl s)) := by
      simp only [mulVec, dotProduct, Pi.add_apply, Pi.sub_apply]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      have := hchi s
      rw [show zStar s + chi Sp s - chi Sm s = zStar s + (chi Sp s - chi Sm s) by ring, this]
      ring
    rw [e]
    simp only [Pi.sub_apply] at h'
    linarith
  have hc := h29 Sm Sp hdisj hz'
  -- (2.9) in integers
  have hlosum : ∑ s ∈ Sm, lo s = (((∑ s ∈ Sm, Lz s : ℤ) : ℝ) : EReal) := by
    rw [← esum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    simp only [hSm, Finset.mem_filter] at hs
    exact hLz' s (lo_fin s hs.2.1)
  have hupsum : ∑ s ∈ Sp, up s = (((∑ s ∈ Sp, Uz s : ℤ) : ℝ) : EReal) := by
    rw [← esum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    simp only [hSp, Finset.mem_filter] at hs
    exact hUz' s (up_fin s hs.2.1)
  rw [hlosum, hupsum] at hc
  have hc' : ∑ s ∈ Sm, Lz s ≤ ∑ s ∈ Sp, Uz s := by
    have := EReal.coe_le_coe_iff.mp hc
    exact_mod_cast this
  -- the cost of the optimal point is at least `ũ(S⁺) - ℓ̃(S⁻) ≥ 0`
  have hper : ∀ s, (Uz s : ℝ) * (xi (Sum.inr s) : ℝ) - (Lz s : ℝ) * (xi (Sum.inl s) : ℝ) ≥
      (if s ∈ Sp then (Uz s : ℝ) else 0) - (if s ∈ Sm then (Lz s : ℝ) else 0) := by
    intro s
    obtain ⟨a0, a1⟩ := hxi01 (Sum.inr s)
    obtain ⟨b0, b1⟩ := hxi01 (Sum.inl s)
    have hmemp : s ∈ Sp ↔ xi (Sum.inr s) = 1 ∧ xi (Sum.inl s) = 0 := by simp [hSp]
    have hmemm : s ∈ Sm ↔ xi (Sum.inl s) = 1 ∧ xi (Sum.inr s) = 0 := by simp [hSm]
    rcases (show xi (Sum.inr s) = 0 ∨ xi (Sum.inr s) = 1 by omega) with ha | ha <;>
    rcases (show xi (Sum.inl s) = 0 ∨ xi (Sum.inl s) = 1 by omega) with hb | hb
    · have hp : s ∉ Sp := by rw [hmemp]; omega
      have hm : s ∉ Sm := by rw [hmemm]; omega
      rw [if_neg hp, if_neg hm, ha, hb]; simp
    · have hp : s ∉ Sp := by rw [hmemp]; omega
      have hm : s ∈ Sm := by rw [hmemm]; omega
      rw [if_neg hp, if_pos hm, ha, hb]; simp
    · have hp : s ∈ Sp := by rw [hmemp]; omega
      have hm : s ∉ Sm := by rw [hmemm]; omega
      rw [if_pos hp, if_neg hm, ha, hb]; simp
    · have hp : s ∉ Sp := by rw [hmemp]; omega
      have hm : s ∉ Sm := by rw [hmemm]; omega
      have hle : (Lz s : ℝ) ≤ (Uz s : ℝ) := by
        have := hlu s
        rw [hLz' s (lo_fin s hb), hUz' s (up_fin s ha)] at this
        exact EReal.coe_le_coe_iff.mp this
      rw [if_neg hp, if_neg hm, ha, hb]; simp; exact_mod_cast hle
  have hcost_eq : ∑ t, (cost t : ℝ) * xs t =
      ∑ s, ((Uz s : ℝ) * (xi (Sum.inr s) : ℝ) - (Lz s : ℝ) * (xi (Sum.inl s) : ℝ)) := by
    rw [Fintype.sum_sum_type, Finset.sum_sub_distrib]
    simp only [hcost, Sum.elim_inl, Sum.elim_inr, hxi, Int.cast_neg, neg_mul,
      Finset.sum_neg_distrib]
    ring
  have hge : ∑ t, (cost t : ℝ) * xs t ≥
      ((∑ s ∈ Sp, Uz s : ℤ) : ℝ) - ((∑ s ∈ Sm, Lz s : ℤ) : ℝ) := by
    rw [hcost_eq]
    calc ∑ s, ((Uz s : ℝ) * (xi (Sum.inr s) : ℝ) - (Lz s : ℝ) * (xi (Sum.inl s) : ℝ))
        ≥ ∑ s, ((if s ∈ Sp then (Uz s : ℝ) else 0) - (if s ∈ Sm then (Lz s : ℝ) else 0)) :=
          Finset.sum_le_sum (fun s _ => hper s)
      _ = ((∑ s ∈ Sp, Uz s : ℤ) : ℝ) - ((∑ s ∈ Sm, Lz s : ℤ) : ℝ) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
          push_cast
          simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have : ((∑ s ∈ Sm, Lz s : ℤ) : ℝ) ≤ ((∑ s ∈ Sp, Uz s : ℤ) : ℝ) := by exact_mod_cast hc'
  linarith
