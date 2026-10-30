-- Prove2me | solution 1 for BoxTDIMinMax.Separable.proposition_2_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:28:35.243632+00:00
-- url     : https://prove2.me/submissions/787e99bd-7f70-4842-80ba-2e8883037aaa

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting
import Theorems.Thm_LP_strong_duality_matrix
import Theorems.Thm_LP_farkas
import Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_1

open Matrix BoxTDIMinMax.Separable

namespace BoxTDIMinMax.Separable.Prop29Aux

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

/-- Adding rows that are superfluous for `{x : M x ≥ r}` preserves TDI: the new system is
indexed by `κ'`, `φ : κ → κ'` embeds the old rows, and every row of the new system is valid
on the old polyhedron. -/
theorem tdi_extend {κ κ' S : Type*} [Fintype κ] [Fintype κ'] [Fintype S] [DecidableEq S]
    (M : Matrix κ S ℚ) (r : κ → ℚ) (M' : Matrix κ' S ℚ) (r' : κ' → ℚ) (φ : κ → κ')
    (hrow : ∀ k, M' (φ k) = M k) (hrhs : ∀ k, r' (φ k) = r k)
    (hsup : ∀ x, Feas M r x → Feas M' r' x) (hT : IsTDI M r) : IsTDI M' r' := by
  classical
  intro c hfe hbdd
  have back : ∀ x, Feas M' r' x → Feas M r x := by
    intro x hx k
    have := hx (φ k)
    rw [hrhs] at this
    simpa only [hrow] using this
  obtain ⟨xs, Ys, hxs, hYs, hval, hopt⟩ := strong M' r' c (primal_feas M' r' c hfe hbdd) hfe
  have hoptM : ∀ x, Feas M r x → ∑ s, (c s : ℝ) * xs s ≤ ∑ s, (c s : ℝ) * x s :=
    fun x hx => hopt x (hsup x hx)
  have hfeM := dual_feas M r c xs (back xs hxs) hoptM
  have hbddM : BddAbove (dualObj r '' DualFeas M c) := by
    refine ⟨∑ s, (c s : ℝ) * xs s, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact weak M r c y hy xs (back xs hxs)
  obtain ⟨y, hyF, hyopt⟩ := hT c hfeM hbddM
  obtain ⟨x2, y2, hx2, hy2, hval2, hopt2⟩ := strong M r c ⟨xs, back xs hxs⟩ hfeM
  have heq : ∑ s, (c s : ℝ) * x2 s = ∑ s, (c s : ℝ) * xs s :=
    le_antisymm (hopt2 xs (back xs hxs)) (hoptM x2 hx2)
  have hyval : ∑ s, (c s : ℝ) * xs s ≤ dualObj r (fun k => (y k : ℝ)) := by
    rw [← heq, hval2]; exact hyopt y2 hy2
  obtain ⟨hy0, hyA⟩ := (feas_iff M c _).mp hyF
  -- push `y` forward along `φ`
  set Y : κ' → ℤ := fun k' => ∑ k ∈ Finset.univ.filter (fun k => φ k = k'), y k with hYdef
  have push : ∀ F : κ' → ℝ, ∑ k', (Y k' : ℝ) * F k' = ∑ k, (y k : ℝ) * F (φ k) := by
    intro F
    simp only [hYdef, Int.cast_sum, Finset.sum_mul]
    rw [← Finset.sum_fiberwise Finset.univ φ (fun k => (y k : ℝ) * F (φ k))]
    refine Finset.sum_congr rfl (fun k' _ => Finset.sum_congr rfl (fun k hk => ?_))
    rw [(Finset.mem_filter.mp hk).2]
  have hYF : (fun k' => (Y k' : ℝ)) ∈ DualFeas M' c := by
    refine (feas_iff M' c _).mpr ⟨fun k' => ?_, fun s => ?_⟩
    · simp only [hYdef, Int.cast_sum]
      exact Finset.sum_nonneg (fun k _ => hy0 k)
    · rw [push (fun k' => (M' k' s : ℝ))]
      simp only [hrow]
      exact hyA s
  have hYobj : dualObj r' (fun k' => (Y k' : ℝ)) = dualObj r (fun k => (y k : ℝ)) := by
    unfold dualObj
    rw [push (fun k' => (r' k' : ℝ))]
    simp only [hrhs]
  refine ⟨Y, hYF, fun Y' hY' => ?_⟩
  rw [hYobj]
  exact (weak M' r' c Y' hY' xs hxs).trans hyval

end BoxTDIMinMax.Separable.Prop29Aux


namespace BoxTDIMinMax.Separable.Prop29Aux

theorem row_box {ι S : Type*} [Fintype S] [DecidableEq S] {κ : Type*} (M : Matrix κ S ℚ)
    (x : S → ℝ) :
    (∀ k, ∑ s, ((boxMat M (Sum.inl k) s : ℚ) : ℝ) * x s = ∑ s, (M k s : ℝ) * x s) ∧
    (∀ t, ∑ s, ((boxMat M (Sum.inr (Sum.inl t)) s : ℚ) : ℝ) * x s = x t) ∧
    (∀ t, ∑ s, ((boxMat M (Sum.inr (Sum.inr t)) s : ℚ) : ℝ) * x s = -x t) := by
  refine ⟨fun k => ?_, fun t => ?_, fun t => ?_⟩
  · simp [boxMat]
  · simp [boxMat, Matrix.one_apply, ite_mul, apply_ite]
  · simp [boxMat, Matrix.one_apply, ite_mul, apply_ite]

end BoxTDIMinMax.Separable.Prop29Aux

open BoxTDIMinMax.Separable.Prop29Aux in
theorem solution {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (Tf Tg : Finset S) (f' g' : S → ℚ) (hfg : ∀ s ∈ Tf, s ∈ Tg → f' s ≤ g' s) :
    IsBoxTDI (partBoxMat (ratMat Q) Tf Tg) (partBoxRhs (ratVec p) Tf Tg f' g') ∧
      IsTDI (partBoxMat (ratMat Q) Tf Tg) (partBoxRhs (ratVec p) Tf Tg f' g') := by
  set A := ratMat Q
  set b := ratVec p
  have hB : IsBoxTDI (partBoxMat A Tf Tg) (partBoxRhs b Tf Tg f' g') := by
    intro f g hfg0
    set M' := boxMat (partBoxMat A Tf Tg)
    set r' := boxRhs (partBoxRhs b Tf Tg f' g') f g
    -- row values of the new system
    have rowM' : ∀ (x : S → ℝ),
        (∀ i, ∑ s, ((M' (Sum.inl (Sum.inl i)) s : ℚ) : ℝ) * x s = ∑ s, (A i s : ℝ) * x s) ∧
        (∀ t : Tf, ∑ s, ((M' (Sum.inl (Sum.inr (Sum.inl t))) s : ℚ) : ℝ) * x s = x t.1) ∧
        (∀ t : Tg, ∑ s, ((M' (Sum.inl (Sum.inr (Sum.inr t))) s : ℚ) : ℝ) * x s = -x t.1) ∧
        (∀ t, ∑ s, ((M' (Sum.inr (Sum.inl t)) s : ℚ) : ℝ) * x s = x t) ∧
        (∀ t, ∑ s, ((M' (Sum.inr (Sum.inr t)) s : ℚ) : ℝ) * x s = -x t) := by
      intro x
      obtain ⟨h1, h2, h3⟩ := row_box (ι := ι) (partBoxMat A Tf Tg) x
      refine ⟨fun i => ?_, fun t => ?_, fun t => ?_, h2, h3⟩
      · rw [h1]; simp [partBoxMat]
      · rw [h1]; simp [partBoxMat, ite_mul, apply_ite]
      · rw [h1]; simp [partBoxMat, ite_mul, apply_ite]
    set f0 : S → ℚ := fun s => if s ∈ Tf ∧ f s ≤ f' s then f' s else f s
    set g0 : S → ℚ := fun s => if s ∈ Tg ∧ g' s ≤ g s then g' s else g s
    -- every point of the new system satisfies `f0 ≤ x ≤ g0`
    have bounds : ∀ x, Feas M' r' x → ∀ s, (f0 s : ℝ) ≤ x s ∧ x s ≤ (g0 s : ℝ) := by
      intro x hx s
      obtain ⟨-, h2, h3, h4, h5⟩ := rowM' x
      constructor
      · simp only [f0]
        split_ifs with h
        · have := hx (Sum.inl (Sum.inr (Sum.inl ⟨s, h.1⟩)))
          rw [h2] at this
          simpa [r', boxRhs, partBoxRhs] using this
        · have := hx (Sum.inr (Sum.inl s))
          rw [h4] at this
          simpa [r', boxRhs] using this
      · simp only [g0]
        split_ifs with h
        · have := hx (Sum.inl (Sum.inr (Sum.inr ⟨s, h.1⟩)))
          rw [h3] at this
          simp only [r', boxRhs, partBoxRhs, Sum.elim_inl, Sum.elim_inr, Rat.cast_neg] at this
          linarith
        · have := hx (Sum.inr (Sum.inr s))
          rw [h5] at this
          simp only [r', boxRhs, Sum.elim_inr, Pi.neg_apply, Rat.cast_neg] at this
          linarith
    by_cases hfg1 : f0 ≤ g0
    swap
    · -- the new system is infeasible, so TDI holds vacuously
      intro c hfe hbdd
      exfalso
      obtain ⟨x, hx⟩ := primal_feas M' r' c hfe hbdd
      apply hfg1
      intro s
      obtain ⟨h1, h2⟩ := bounds x hx s
      have : (f0 s : ℝ) ≤ (g0 s : ℝ) := h1.trans h2
      exact_mod_cast this
    · let φ : ι ⊕ (S ⊕ S) → (ι ⊕ (Tf ⊕ Tg)) ⊕ (S ⊕ S) := fun k => match k with
        | Sum.inl i => Sum.inl (Sum.inl i)
        | Sum.inr (Sum.inl s) =>
            if h : s ∈ Tf ∧ f s ≤ f' s then Sum.inl (Sum.inr (Sum.inl ⟨s, h.1⟩))
            else Sum.inr (Sum.inl s)
        | Sum.inr (Sum.inr s) =>
            if h : s ∈ Tg ∧ g' s ≤ g s then Sum.inl (Sum.inr (Sum.inr ⟨s, h.1⟩))
            else Sum.inr (Sum.inr s)
      refine tdi_extend (boxMat A) (boxRhs b f0 g0) M' r' φ (fun k => ?_) (fun k => ?_)
        (fun x hx k => ?_) (hbox f0 g0 hfg1)
      · rcases k with i | s | s
        · funext t; simp [φ, M', boxMat, partBoxMat]
        · by_cases h : s ∈ Tf ∧ f s ≤ f' s
          · funext t; simp only [φ, dif_pos h]
            simp [M', boxMat, partBoxMat, Matrix.one_apply, eq_comm]
          · funext t; simp only [φ, dif_neg h]
            simp [M', boxMat]
        · by_cases h : s ∈ Tg ∧ g' s ≤ g s
          · funext t; simp only [φ, dif_pos h]
            simp [M', boxMat, partBoxMat, Matrix.one_apply, eq_comm]
            split_ifs <;> simp
          · funext t; simp only [φ, dif_neg h]
            simp [M', boxMat]
      · rcases k with i | s | s
        · simp [φ, r', boxRhs, partBoxRhs]
        · by_cases h : s ∈ Tf ∧ f s ≤ f' s
          · simp only [φ, dif_pos h]; simp [r', boxRhs, partBoxRhs, f0, h]
          · simp only [φ, dif_neg h]; simp [r', boxRhs, f0, h]
        · by_cases h : s ∈ Tg ∧ g' s ≤ g s
          · simp only [φ, dif_pos h]; simp [r', boxRhs, partBoxRhs, g0, h]
          · simp only [φ, dif_neg h]; simp [r', boxRhs, g0, h]
      · -- validity of every new row on `[A x ≥ b, f0 ≤ x ≤ g0]`
        obtain ⟨b1, b2, b3⟩ := row_box (ι := ι) A x
        have hA : ∀ i, (b i : ℝ) ≤ ∑ s, (A i s : ℝ) * x s := by
          intro i; have := hx (Sum.inl i); rw [b1] at this; simpa [boxRhs] using this
        have hlo : ∀ s, (f0 s : ℝ) ≤ x s := by
          intro s; have := hx (Sum.inr (Sum.inl s)); rw [b2] at this; simpa [boxRhs] using this
        have hhi : ∀ s, x s ≤ (g0 s : ℝ) := by
          intro s; have := hx (Sum.inr (Sum.inr s)); rw [b3] at this
          simp only [boxRhs, Sum.elim_inr, Pi.neg_apply, Rat.cast_neg] at this; linarith
        obtain ⟨h1, h2, h3, h4, h5⟩ := rowM' x
        rcases k with (i | t | t) | t | t
        · rw [h1]; simpa [r', boxRhs, partBoxRhs] using hA i
        · rw [h2]
          have hl := hlo t.1
          have : (f' t.1 : ℝ) ≤ (f0 t.1 : ℝ) := by
            simp only [f0]; split_ifs with h
            · exact le_rfl
            · have : f' t.1 < f t.1 := by
                by_contra hc; exact h ⟨t.2, not_lt.mp hc⟩
              exact_mod_cast this.le
          simp only [r', boxRhs, partBoxRhs, Sum.elim_inl, Sum.elim_inr]; linarith
        · rw [h3]
          have hh := hhi t.1
          have : (g0 t.1 : ℝ) ≤ (g' t.1 : ℝ) := by
            simp only [g0]; split_ifs with h
            · exact le_rfl
            · have : g t.1 < g' t.1 := by
                by_contra hc; exact h ⟨t.2, not_lt.mp hc⟩
              exact_mod_cast this.le
          simp only [r', boxRhs, partBoxRhs, Sum.elim_inl, Sum.elim_inr, Rat.cast_neg]; linarith
        · rw [h4]
          have hl := hlo t
          have : (f t : ℝ) ≤ (f0 t : ℝ) := by
            simp only [f0]; split_ifs with h
            · exact_mod_cast h.2
            · exact le_rfl
          simp only [r', boxRhs, Sum.elim_inr, Sum.elim_inl]; linarith
        · rw [h5]
          have hh := hhi t
          have : (g0 t : ℝ) ≤ (g t : ℝ) := by
            simp only [g0]; split_ifs with h
            · exact_mod_cast h.2
            · exact le_rfl
          simp only [r', boxRhs, Sum.elim_inr, Pi.neg_apply, Rat.cast_neg]; linarith
  exact ⟨hB, proposition_2_1 _ _ hB⟩
