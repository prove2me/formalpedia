-- Prove2me | solution 3 for DDMomentDRO.Type3.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:35:17.081237+00:00
-- url     : https://prove2.me/submissions/cceada1e-e1af-4d85-9e4e-f91664f67e5e

import Mathlib
import Definitions.Def_DDMomentDRO_Type3_Setting
import Theorems.Thm_Lagrange_exists_multiplier

-- carved verbatim out of submission f73a10cc-24a9-4010-93bb-583a4fe2a48e, lines 1678-1711

section
open Matrix
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem isLeast_add_isGreatest_iff {X : Type*} (S : Set X) (g : X → ℝ)
    (W D : X → Set ℝ) (h : ∀ x ∈ S, ∃ w, IsGreatest (W x) w ∧ IsLeast (D x) w) (q : ℝ) :
    IsLeast {v | ∃ x ∈ S, ∃ w, IsGreatest (W x) w ∧ v = g x + w} q ↔
      IsLeast {v | ∃ x ∈ S, ∃ d ∈ D x, v = g x + d} q := by
  have key : ∀ x ∈ S, ∀ w, IsGreatest (W x) w → IsLeast (D x) w := by
    intro x hx w hw
    obtain ⟨w', hw', hd'⟩ := h x hx
    rw [hw.unique hw']
    exact hd'
  constructor
  · rintro ⟨⟨x, hx, w, hw, rfl⟩, hlow⟩
    refine ⟨⟨x, hx, w, (key x hx w hw).1, rfl⟩, ?_⟩
    rintro _ ⟨x', hx', d', hd', rfl⟩
    obtain ⟨w', hw', hdw'⟩ := h x' hx'
    have h1 := hlow ⟨x', hx', w', hw', rfl⟩
    have h2 := hdw'.2 hd'
    linarith
  · rintro ⟨⟨x, hx, d, hd, rfl⟩, hlow⟩
    obtain ⟨w, hw, hdw⟩ := h x hx
    have h1 := hdw.2 hd
    have h2 := hlow ⟨x, hx, w, hdw.1, rfl⟩
    refine ⟨⟨x, hx, w, hw, by linarith⟩, ?_⟩
    rintro _ ⟨x', hx', w', hw', rfl⟩
    exact hlow ⟨x', hx', w', (key x' hx' w' hw').1, rfl⟩

def psdForm (n : Type*) [Fintype n] : PointedCone ℝ (Matrix n n ℝ) where
  carrier := {A | ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ A *ᵥ v}
  add_mem' := by
    intro A B hA hB v
    simp only [Set.mem_ofPred_eq, Matrix.add_mulVec, dotProduct_add] at *
    exact add_nonneg (hA v) (hB v)
  zero_mem' := by intro v; simp
  smul_mem' := by
    intro t A hA v
    have h : (0 : ℝ) ≤ (t : ℝ) * (v ⬝ᵥ A *ᵥ v) := mul_nonneg t.2 (hA v)
    simp only [Matrix.smul_mulVec, dotProduct_smul]
    exact h

private lemma aux2_mem_psdForm {n : Type*} [Fintype n] {A : Matrix n n ℝ} :
    A ∈ psdForm n ↔ ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ A *ᵥ v := Iff.rfl

private lemma aux2_isHermitian {n : Type*} {A : Matrix n n ℝ} (hA : A.IsSymm) : A.IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hA

private lemma aux2_dot_self_nonneg {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

private lemma aux2_dot_self_pos {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (aux2_dot_self_nonneg v) (Ne.symm (mt dotProduct_self_eq_zero.1 hv))

private lemma aux2_qf_smul {n : Type*} [Fintype n] (A : Matrix n n ℝ) (c : ℝ) (v : n → ℝ) :
    (c • v) ⬝ᵥ A *ᵥ (c • v) = c ^ 2 * (v ⬝ᵥ A *ᵥ v) := by
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

private lemma aux2_normalize {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (c • v) ⬝ᵥ (c • v) = 1 := by
  have hpos := aux2_dot_self_pos hv
  have hs : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.2 hpos
  have hs2 : Real.sqrt (v ⬝ᵥ v) ^ 2 = v ⬝ᵥ v := Real.sq_sqrt hpos.le
  refine ⟨(Real.sqrt (v ⬝ᵥ v))⁻¹, inv_pos.2 hs, ?_⟩
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  field_simp
  linarith [hs2]

private def aux2_sph (n : Type*) [Fintype n] : Set (n → ℝ) := {v | v ⬝ᵥ v = 1}

private lemma aux2_sph_compact (n : Type*) [Fintype n] : IsCompact (aux2_sph n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun v hv => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : v i * v i ≤ v ⬝ᵥ v :=
      Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
        (Finset.mem_univ i)
    have h2 : v ⬝ᵥ v = 1 := hv
    rw [Real.norm_eq_abs]
    nlinarith [abs_mul_abs_self (v i), abs_nonneg (v i)]

private lemma aux2_sph_ne {n : Type*} [Fintype n] {v : n → ℝ} (hv : v ∈ aux2_sph n) : v ≠ 0 := by
  rintro rfl; simp [aux2_sph] at hv

private lemma aux2_trace_vecMulVec {n : Type*} [Fintype n] (M : Matrix n n ℝ) (x : n → ℝ) :
    (M * vecMulVec x x).trace = x ⬝ᵥ M *ᵥ x := by
  simp only [trace, diag, mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma aux2_vecMulVec_mem {n : Type*} [Fintype n] (v : n → ℝ) : vecMulVec v v ∈ psdForm n := by
  intro w
  simpa using (posSemidef_vecMulVec_self_star v).dotProduct_mulVec_nonneg w

open scoped MatrixOrder in
private lemma aux2_trace_mul_nonneg {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  have hB0 : 0 ≤ B := hB.nonneg
  have hS : (CFC.sqrt B).PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hSS : CFC.sqrt B * CFC.sqrt B = B := CFC.sqrt_mul_sqrt_self B hB0
  have hSh : (CFC.sqrt B)ᴴ = CFC.sqrt B := hS.isHermitian.eq
  have h := (hA.mul_mul_conjTranspose_same (CFC.sqrt B)).trace_nonneg
  rw [hSh] at h
  rw [← hSS, ← mul_assoc, trace_mul_cycle]
  exact h

theorem mem_psdForm_iff_posSemidef {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsSymm) :
    A ∈ psdForm n ↔ A.PosSemidef := by
  rw [aux2_mem_psdForm, posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h; exact ⟨aux2_isHermitian hA, fun x => by simpa using h x⟩
  · rintro ⟨-, h⟩ v; simpa using h v

theorem Matrix.PosDef.mem_interior_psdForm {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    A ∈ interior (psdForm n : Set (Matrix n n ℝ)) := by
  rw [mem_interior_iff_mem_nhds]
  have hpos : ∀ v ∈ aux2_sph n, 0 < v ⬝ᵥ A *ᵥ v := fun v hv => by
    simpa using hA.dotProduct_mulVec_pos (aux2_sph_ne hv)
  have hcont : Continuous (fun z : Matrix n n ℝ × (n → ℝ) => z.2 ⬝ᵥ z.1 *ᵥ z.2) :=
    continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd)
  have hev := (aux2_sph_compact n).eventually_forall_of_forall_eventually (x₀ := A)
    (P := fun B v => 0 < v ⬝ᵥ B *ᵥ v)
    (fun v hv => hcont.continuousAt.eventually (lt_mem_nhds (hpos v hv)))
  filter_upwards [hev] with B hB
  intro v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨c, hc, hcv⟩ := aux2_normalize hv
  have h := hB _ hcv
  rw [aux2_qf_smul] at h
  exact (pos_of_mul_pos_right h (sq_nonneg c)).le

theorem psdForm_dual {n : Type*} [Fintype n] [DecidableEq n] (y : Module.Dual ℝ (Matrix n n ℝ))
    (hy : ∀ A ∈ psdForm n, 0 ≤ y A) : ∃ Y : Matrix n n ℝ, Y.PosSemidef ∧ ∀ A, y A = (Yᵀ * A).trace := by
  let Y : Matrix n n ℝ := fun i j => y (Matrix.single i j 1)
  have hrep : ∀ A, y A = (Yᵀ * A).trace := by
    intro A
    conv_lhs => rw [matrix_eq_sum_single A]
    have hs : ∀ i j, y (Matrix.single i j (A i j)) = A i j * Y i j := by
      intro i j
      have : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℝ) := by
        rw [smul_single, smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
    simp only [map_sum, hs, trace, diag, mul_apply, transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hanti : ∀ i j, Matrix.single i j (1 : ℝ) - Matrix.single j i 1 ∈ psdForm n := by
    intro i j v
    have : v ⬝ᵥ (Matrix.single i j (1 : ℝ) - Matrix.single j i 1) *ᵥ v = 0 := by
      simp only [sub_mulVec, dotProduct_sub, single_mulVec, one_mul]
      change v ⬝ᵥ Pi.single i (v j) - v ⬝ᵥ Pi.single j (v i) = 0
      simp only [dotProduct_single]
      ring
    rw [this]
  have hsymm : Yᵀ = Y := by
    ext i j
    have h1 := hy _ (hanti i j)
    have h2 := hy _ (hanti j i)
    simp only [map_sub] at h1 h2
    show y (Matrix.single j i 1) = y (Matrix.single i j 1)
    linarith
  refine ⟨Y, ?_, hrep⟩
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · exact aux2_isHermitian hsymm
  · have h := hy _ (aux2_vecMulVec_mem x)
    rw [hrep, aux2_trace_vecMulVec, hsymm] at h
    simpa using h

theorem Matrix.PosSemidef.trace_mul_nonneg {n : Type*} [Fintype n] {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := aux2_trace_mul_nonneg hA hB

theorem Matrix.isClosed_setOf_posSemidef {n : Type*} [Fintype n] : IsClosed {A : Matrix n n ℝ | A.PosSemidef} := by
  have : {A : Matrix n n ℝ | A.PosSemidef} =
      {A | Aᴴ = A} ∩ ⋂ x : n → ℝ, {A | 0 ≤ star x ⬝ᵥ A *ᵥ x} := by
    ext A; simp only [Set.mem_ofPred_eq, posSemidef_iff_dotProduct_mulVec, IsHermitian,
      Set.mem_inter_iff, Set.mem_iInter]
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

end

section
open Matrix DDMomentDRO.Type3
variable {J : ℕ} (A : Matrix (Fin J) (Fin J) ℝ) (d : Fin J → ℝ) (c : ℝ)

@[simp] lemma b2_ll (i j : Fin J) : block2 A d c (Sum.inl i) (Sum.inl j) = A i j := rfl

@[simp] lemma b2_lr (i : Fin J) (u : Unit) : block2 A d c (Sum.inl i) (Sum.inr u) = d i := rfl

@[simp] lemma b2_rl (u : Unit) (j : Fin J) : block2 A d c (Sum.inr u) (Sum.inl j) = d j := rfl

@[simp] lemma b2_rr (u v : Unit) : block2 A d c (Sum.inr u) (Sum.inr v) = c := rfl

end

section
open Matrix DDMomentDRO.Type3

lemma qf_block2 {J : ℕ} (A : Matrix (Fin J) (Fin J) ℝ) (d : Fin J → ℝ) (c : ℝ)
    (v : Fin J ⊕ Unit → ℝ) :
    v ⬝ᵥ (block2 A d c *ᵥ v) = (v ∘ Sum.inl) ⬝ᵥ (A *ᵥ (v ∘ Sum.inl))
      + 2 * v (Sum.inr ()) * (d ⬝ᵥ (v ∘ Sum.inl)) + c * v (Sum.inr ()) ^ 2 := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, b2_ll, b2_lr, b2_rl, b2_rr,
    Finset.univ_unique, Finset.sum_singleton, Function.comp_apply, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ x, v (Sum.inl x) * (d x * v (Sum.inr default))
      = v (Sum.inr ()) * ∑ x, d x * v (Sum.inl x) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : v (Sum.inr default) * ∑ x, d x * v (Sum.inl x)
      = v (Sum.inr ()) * ∑ x, d x * v (Sum.inl x) := rfl
  rw [h1, h2]
  have : (default : Unit) = () := rfl
  simp only [this]
  ring

lemma frob_block2 {J : ℕ} (A B : Matrix (Fin J) (Fin J) ℝ) (d e : Fin J → ℝ) (c f : ℝ) :
    frob (block2 A d c) (block2 B e f) = frob A B + 2 * (d ⬝ᵥ e) + c * f := by
  simp only [frob, trace, diag, mul_apply, transpose_apply, Fintype.sum_sum_type, b2_ll, b2_lr,
    b2_rl, b2_rr, Finset.univ_unique, Finset.sum_singleton, dotProduct, Finset.sum_add_distrib]
  ring

lemma frob_comm {n : Type*} [Fintype n] (A B : Matrix n n ℝ) : frob A B = frob B A := by
  unfold frob
  rw [← trace_transpose, transpose_mul, transpose_transpose]

lemma block2_isHermitian {J : ℕ} {A : Matrix (Fin J) (Fin J) ℝ} (hA : A.IsHermitian)
    (d : Fin J → ℝ) (c : ℝ) : (block2 A d c).IsHermitian := by
  apply IsHermitian.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j <;> simp
  simpa using hA.apply i j

lemma unit_psd_iff (M : Matrix Unit Unit ℝ) : M.PosSemidef ↔ 0 ≤ M () () := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    have := h.2 (fun _ => 1)
    simpa [dotProduct, mulVec] using this
  · intro h
    refine ⟨IsHermitian.ext fun i j => by simp [Subsingleton.elim i j], fun x => ?_⟩
    simp only [dotProduct, mulVec, Finset.univ_unique, Finset.sum_singleton, star_trivial]
    have : M default default = M () () := rfl
    rw [this]
    nlinarith [sq_nonneg (x default)]

lemma block2_psd_iff {J : ℕ} {A : Matrix (Fin J) (Fin J) ℝ} (hA : A.PosDef)
    (d : Fin J → ℝ) (c : ℝ) : (block2 A d c).PosSemidef ↔ d ⬝ᵥ (A⁻¹ *ᵥ d) ≤ c := by
  have := hA.isUnit.invertible
  have hb : block2 A d c = fromBlocks A (replicateCol Unit d) (replicateCol Unit d)ᴴ
      (Matrix.of fun _ _ => c) := by
    rw [conjTranspose_replicateCol, star_trivial]; rfl
  rw [hb, PosDef.fromBlocks₁₁ _ _ hA, unit_psd_iff]
  have : ((Matrix.of fun _ _ => c : Matrix Unit Unit ℝ) - (replicateCol Unit d)ᴴ * A⁻¹ * replicateCol Unit d)
      () () = c - d ⬝ᵥ (A⁻¹ *ᵥ d) := by
    simp [mul_apply, dotProduct, mulVec, Finset.mul_sum, mul_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [this, sub_nonneg]

lemma block2_posDef {J : ℕ} {A : Matrix (Fin J) (Fin J) ℝ} (hA : A.PosDef)
    (d : Fin J → ℝ) (c : ℝ) (hlt : d ⬝ᵥ (A⁻¹ *ᵥ d) < c) : (block2 A d c).PosDef := by
  have hP := (block2_psd_iff hA d (d ⬝ᵥ (A⁻¹ *ᵥ d))).2 le_rfl
  refine PosDef.of_dotProduct_mulVec_pos (block2_isHermitian hA.1 d c) fun v hv => ?_
  have h1 := hP.dotProduct_mulVec_nonneg v
  rw [star_trivial, qf_block2] at h1 ⊢
  by_cases ht : v (Sum.inr ()) = 0
  · have hx : v ∘ Sum.inl ≠ 0 := by
      intro h; apply hv; funext i
      rcases i with i | u
      · exact congrFun h i
      · cases u; exact ht
    have := hA.dotProduct_mulVec_pos hx
    rw [star_trivial] at this
    rw [ht]; simpa using this
  · have ht2 : 0 < v (Sum.inr ()) ^ 2 := by positivity
    have hm := mul_pos (sub_pos.2 hlt) ht2
    have e : (v ∘ Sum.inl) ⬝ᵥ (A *ᵥ (v ∘ Sum.inl)) + 2 * v (Sum.inr ()) * (d ⬝ᵥ (v ∘ Sum.inl))
        + c * v (Sum.inr ()) ^ 2 = ((v ∘ Sum.inl) ⬝ᵥ (A *ᵥ (v ∘ Sum.inl))
        + 2 * v (Sum.inr ()) * (d ⬝ᵥ (v ∘ Sum.inl))
        + d ⬝ᵥ (A⁻¹ *ᵥ d) * v (Sum.inr ()) ^ 2) + (c - d ⬝ᵥ (A⁻¹ *ᵥ d)) * v (Sum.inr ()) ^ 2 := by
      ring
    rw [e]; linarith

lemma frob_psd_nonneg {n : Type*} [Fintype n] {A B : Matrix n n ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ frob A B := by
  unfold frob
  have : Aᵀ = A := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hA.1
  rw [this]; exact Matrix.PosSemidef.trace_mul_nonneg hA hB

lemma frob_smul_sub {n : Type*} [Fintype n] (η : ℝ) (A M Y : Matrix n n ℝ) :
    frob (η • A - M) Y = η * frob A Y - frob M Y := by
  simp [frob, transpose_sub, Matrix.sub_mul, trace_sub, transpose_smul, Matrix.smul_mul, trace_smul]

lemma frob_sum_smul {n : Type*} [Fintype n] {K : ℕ} (p : Fin K → ℝ) (O : Fin K → Matrix n n ℝ)
    (Y : Matrix n n ℝ) : frob (∑ k, p k • O k) Y = ∑ k, p k * frob (O k) Y := by
  simp [frob, transpose_sum, Finset.sum_mul, trace_sum, transpose_smul, Matrix.smul_mul, trace_smul]

lemma weak {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (x : Fin I → ℝ) (hSx : (Sig x).PosDef) {p : Fin K → ℝ} (hp : p ∈ amb3 ξ μ Sig γ η x)
    {s : ℝ} {z1 : Matrix (Fin J) (Fin J) ℝ} {z2 : Fin J → ℝ} {z3 : ℝ}
    {Y : Matrix (Fin J) (Fin J) ℝ} (hD : DualFeas3 Qn ξ μ x s z1 z2 z3 Y) :
    ∑ k, p k * Qn x k ≤ dualObj3 μ Sig γ η x s z1 z2 z3 Y := by
  obtain ⟨hsum, hell, hpsd, hnn⟩ := hp
  obtain ⟨hZ, hY, hk⟩ := hD
  have h1 : ∑ k, p k * Qn x k ≤ ∑ k, p k * (s - 2 * (z2 ⬝ᵥ ξ k) + frob (outerDev ξ μ x k) Y) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hnn k)
  have h2 : ∑ k, p k * (s - 2 * (z2 ⬝ᵥ ξ k) + frob (outerDev ξ μ x k) Y)
      = s - 2 * (z2 ⬝ᵥ meanVec ξ p) + frob (secondMoment ξ μ x p) Y := by
    rw [secondMoment, frob_sum_smul, meanVec, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, Finset.mul_sum]
    ring_nf
  have h3 := frob_psd_nonneg hpsd hY
  rw [frob_smul_sub] at h3
  have h4 := frob_psd_nonneg ((block2_psd_iff hSx _ γ).2 hell) hZ
  rw [frob_block2, sub_dotProduct, dotProduct_comm (meanVec ξ p)] at h4
  unfold dualObj3
  linarith

lemma amb3_isClosed {I J K : ℕ} (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (x : Fin I → ℝ) : IsClosed (amb3 ξ μ Sig γ η x) := by
  have hm : Continuous fun p : Fin K → ℝ => meanVec ξ p - μ x := by
    unfold meanVec; fun_prop
  have hM : Continuous fun p : Fin K → ℝ => η • Sig x - secondMoment ξ μ x p := by
    unfold secondMoment; fun_prop
  have hq : Continuous fun p : Fin K → ℝ =>
      (meanVec ξ p - μ x) ⬝ᵥ ((Sig x)⁻¹ *ᵥ (meanVec ξ p - μ x)) :=
    hm.dotProduct (continuous_const.matrix_mulVec hm)
  refine (isClosed_eq (by fun_prop) continuous_const).inter ((isClosed_le hq continuous_const).inter
    ((Matrix.isClosed_setOf_posSemidef.preimage hM).inter ?_))
  have e : {p : Fin K → ℝ | ∀ k, 0 ≤ p k} = ⋂ k, {p | 0 ≤ p k} := by ext; simp
  change IsClosed {p : Fin K → ℝ | ∀ k, 0 ≤ p k}
  rw [e]
  exact isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)

lemma amb3_isCompact {I J K : ℕ} (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (x : Fin I → ℝ) : IsCompact (amb3 ξ μ Sig γ η x) := by
  refine Metric.isCompact_of_isClosed_isBounded (amb3_isClosed ξ μ Sig γ η x) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin K → ℝ)) (r := 1)).subset ?_
  intro p hp
  obtain ⟨hsum, -, -, hnn⟩ := hp
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn k), ← hsum]
  exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ k)

lemma primal_max {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (x : Fin I → ℝ) (hne : (amb3 ξ μ Sig γ η x).Nonempty) :
    ∃ p ∈ amb3 ξ μ Sig γ η x, IsGreatest (wcVal Qn ξ μ Sig γ η x) (∑ k, p k * Qn x k) := by
  obtain ⟨p, hp, hmax⟩ := (amb3_isCompact ξ μ Sig γ η x).exists_isMaxOn hne
    (f := fun p : Fin K → ℝ => ∑ k, p k * Qn x k) (by fun_prop)
  refine ⟨p, hp, ⟨p, hp, rfl⟩, ?_⟩
  rintro v ⟨p', hp', rfl⟩
  exact hmax hp'

abbrev Fsp (J : ℕ) := Matrix (Fin J ⊕ Unit) (Fin J ⊕ Unit) ℝ × Matrix (Fin J) (Fin J) ℝ

def Gm {I J K : ℕ} (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (x : Fin I → ℝ) (p : Fin K → ℝ) : Fsp J :=
  (block2 (Sig x) (meanVec ξ p - μ x) γ, η • Sig x - secondMoment ξ μ x p)

def Kc (J : ℕ) : PointedCone ℝ (Fsp J) :=
  (psdForm (Fin J ⊕ Unit)).prod (psdForm (Fin J))

def simplex (K : ℕ) : Set (Fin K → ℝ) := {p | (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1}

lemma meanVec_comb {J K : ℕ} (ξ : Fin K → Fin J → ℝ) (t : ℝ) (p1 p2 : Fin K → ℝ) :
    meanVec ξ (t • p1 + (1 - t) • p2) = t • meanVec ξ p1 + (1 - t) • meanVec ξ p2 := by
  simp [meanVec, add_smul, smul_smul, Finset.sum_add_distrib, Finset.smul_sum]

lemma secondMoment_comb {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (x : Fin I → ℝ) (t : ℝ) (p1 p2 : Fin K → ℝ) :
    secondMoment ξ μ x (t • p1 + (1 - t) • p2)
      = t • secondMoment ξ μ x p1 + (1 - t) • secondMoment ξ μ x p2 := by
  simp [secondMoment, add_smul, smul_smul, Finset.sum_add_distrib, Finset.smul_sum]

lemma Gm_comb {I J K : ℕ} (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (x : Fin I → ℝ) (t : ℝ) (p1 p2 : Fin K → ℝ) :
    Gm ξ μ Sig γ η x (t • p1 + (1 - t) • p2)
      = t • Gm ξ μ Sig γ η x p1 + (1 - t) • Gm ξ μ Sig γ η x p2 := by
  ext i j
  · rcases i with i | u <;> rcases j with j | v <;>
      simp [Gm, meanVec_comb] <;> ring
  · simp [Gm, secondMoment_comb]; ring

lemma isSymm_of_isHermitian {n : Type*} {A : Matrix n n ℝ} (h : A.IsHermitian) : A.IsSymm := by
  unfold IsSymm; rw [← conjTranspose_eq_transpose_of_trivial]; exact h

lemma secondMoment_isHermitian {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (x : Fin I → ℝ) (p : Fin K → ℝ) : (secondMoment ξ μ x p).IsHermitian := by
  apply IsHermitian.ext
  intro i j
  simp [secondMoment, outerDev, Matrix.sum_apply, vecMulVec_apply, mul_comm]

lemma mem_Kc_iff {I J K : ℕ} (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (x : Fin I → ℝ) (hSx : (Sig x).PosDef) (p : Fin K → ℝ) :
    Gm ξ μ Sig γ η x p ∈ Kc J ↔ (block2 (Sig x) (meanVec ξ p - μ x) γ).PosSemidef ∧
      (η • Sig x - secondMoment ξ μ x p).PosSemidef := by
  rw [Kc, Submodule.mem_prod]
  have h1 := isSymm_of_isHermitian (block2_isHermitian hSx.1 (meanVec ξ p - μ x) γ)
  have h2 : (η • Sig x - secondMoment ξ μ x p).IsSymm :=
    ((isSymm_of_isHermitian hSx.1).smul η).sub
      (isSymm_of_isHermitian (secondMoment_isHermitian ξ μ x p))
  exact and_congr (mem_psdForm_iff_posSemidef h1)
    (mem_psdForm_iff_posSemidef h2)

lemma meanVec_single {J K : ℕ} (ξ : Fin K → Fin J → ℝ) (k : Fin K) :
    meanVec ξ (Pi.single k 1) = ξ k := by
  simp [meanVec, Pi.single_apply, ite_smul]

lemma secondMoment_single {I J K : ℕ} (ξ : Fin K → Fin J → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (x : Fin I → ℝ) (k : Fin K) :
    secondMoment ξ μ x (Pi.single k 1) = outerDev ξ μ x k := by
  simp [secondMoment, Pi.single_apply, ite_smul]

lemma single_mem_simplex {K : ℕ} (k : Fin K) : (Pi.single k 1 : Fin K → ℝ) ∈ simplex K := by
  refine ⟨fun j => ?_, by simp⟩
  by_cases h : j = k
  · subst h; simp
  · simp [h]

lemma strong {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (x : Fin I → ℝ) (hSx : (Sig x).PosDef)
    (hsl : ∃ p : Fin K → ℝ, IsSlaterPoint ξ μ Sig γ η x p) :
    ∃ w, IsGreatest (wcVal Qn ξ μ Sig γ η x) w ∧
      IsLeast {d | ∃ s z1 z2 z3 Y, DualFeas3 Qn ξ μ x s z1 z2 z3 Y ∧
        d = dualObj3 μ Sig γ η x s z1 z2 z3 Y} w := by
  obtain ⟨p0, h0nn, h0sum, h0ell, h0pd⟩ := hsl
  have hp0 : p0 ∈ amb3 ξ μ Sig γ η x := ⟨h0sum, h0ell.le, h0pd.posSemidef, h0nn⟩
  obtain ⟨ps, hps, hG⟩ := primal_max Qn ξ μ Sig γ η x ⟨p0, hp0⟩
  refine ⟨_, hG, ?_, ?_⟩
  swap
  · rintro d ⟨s, z1, z2, z3, Y, hD, rfl⟩
    exact weak Qn ξ μ Sig γ η x hSx hps hD
  -- Lagrange multipliers
  have hcvx : ∀ p1 ∈ simplex K, ∀ p2 ∈ simplex K, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ p ∈ simplex K,
      Gm ξ μ Sig γ η x p - (t • Gm ξ μ Sig γ η x p1 + (1 - t) • Gm ξ μ Sig γ η x p2) ∈ Kc J ∧
      t * (∑ k, p1 k * Qn x k) + (1 - t) * (∑ k, p2 k * Qn x k) ≤ ∑ k, p k * Qn x k := by
    intro p1 h1 p2 h2 t ht0 ht1
    refine ⟨t • p1 + (1 - t) • p2, ⟨fun k => ?_, ?_⟩, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ht0 (h1.1 k)) (mul_nonneg (sub_nonneg.2 ht1) (h2.1 k))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, h1.2, h2.2]
      ring
    · rw [Gm_comb, sub_self]; exact zero_mem _
    · apply le_of_eq
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
  have hint : Gm ξ μ Sig γ η x p0 ∈ interior (Kc J : Set (Fsp J)) := by
    rw [Kc, Submodule.prod_coe, interior_prod_eq]
    exact ⟨Matrix.PosDef.mem_interior_psdForm (block2_posDef hSx _ γ h0ell),
      Matrix.PosDef.mem_interior_psdForm h0pd⟩
  have hslater : (0 : Fsp J) ∈ interior
      {u | ∃ p ∈ simplex K, Gm ξ μ Sig γ η x p - u ∈ Kc J} := by
    have hopen := (isOpen_interior (s := (Kc J : Set (Fsp J)))).preimage
      (continuous_const.sub continuous_id : Continuous fun u : Fsp J => Gm ξ μ Sig γ η x p0 - u)
    refine mem_interior.2 ⟨_, ?_, hopen, by simpa using hint⟩
    intro u hu
    exact ⟨p0, ⟨h0nn, h0sum⟩, interior_subset hu⟩
  have hp : ∀ p ∈ simplex K, Gm ξ μ Sig γ η x p ∈ Kc J →
      ∑ k, p k * Qn x k ≤ ∑ k, ps k * Qn x k := by
    intro p hp hGK
    obtain ⟨h1, h2⟩ := (mem_Kc_iff ξ μ Sig γ η x hSx p).1 hGK
    exact hG.2 ⟨p, ⟨hp.2, (block2_psd_iff hSx _ γ).1 h1, h2, hp.1⟩, rfl⟩
  obtain ⟨y, hyK, hy⟩ := Lagrange.exists_multiplier (simplex K)
    (fun p => ∑ k, p k * Qn x k) (Gm ξ μ Sig γ η x) (Kc J) hcvx hslater _ hp
  let y1 : Module.Dual ℝ (Matrix (Fin J ⊕ Unit) (Fin J ⊕ Unit) ℝ) := y.comp (LinearMap.inl ℝ _ _)
  let y2 : Module.Dual ℝ (Matrix (Fin J) (Fin J) ℝ) := y.comp (LinearMap.inr ℝ _ _)
  have hy12 : ∀ A B, y (A, B) = y1 A + y2 B := by
    intro A B
    have : ((A, B) : Fsp J) = (A, 0) + (0, B) := by simp
    rw [this, map_add]; rfl
  have hy1 : ∀ A ∈ psdForm (Fin J ⊕ Unit), 0 ≤ y1 A := fun A hA =>
    hyK _ (Submodule.mem_prod.2 ⟨hA, zero_mem _⟩)
  have hy2 : ∀ B ∈ psdForm (Fin J), 0 ≤ y2 B := fun B hB =>
    hyK _ (Submodule.mem_prod.2 ⟨zero_mem _, hB⟩)
  obtain ⟨Z, hZ, hZe⟩ := psdForm_dual y1 hy1
  obtain ⟨Y, hY, hYe⟩ := psdForm_dual y2 hy2
  let z1 : Matrix (Fin J) (Fin J) ℝ := Matrix.of fun i j => Z (Sum.inl i) (Sum.inl j)
  let z2 : Fin J → ℝ := fun i => Z (Sum.inl i) (Sum.inr ())
  let z3 : ℝ := Z (Sum.inr ()) (Sum.inr ())
  have hZb : Z = block2 z1 z2 z3 := by
    ext i j
    rcases i with i | u <;> rcases j with j | v
    · rfl
    · cases v; rfl
    · cases u
      have := hZ.1.apply (Sum.inr ()) (Sum.inl j)
      rw [star_trivial] at this
      exact this.symm
    · cases u; cases v; rfl
  refine ⟨(∑ j, ps j * Qn x j) - (frob (Sig x) z1 - 2 * (μ x ⬝ᵥ z2) + γ * z3 + η * frob (Sig x) Y),
    z1, z2, z3, Y, ⟨hZb ▸ hZ, hY, fun k => ?_⟩, by unfold dualObj3; ring⟩
  have hk := hy (Pi.single k 1) (single_mem_simplex k)
  simp only [Gm, hy12, hZe, hYe, meanVec_single, secondMoment_single] at hk
  have hQ : ∑ j, (Pi.single k 1 : Fin K → ℝ) j * Qn x j = Qn x k := by simp [Pi.single_apply]
  rw [hQ] at hk
  change Qn x k + (frob Z (block2 (Sig x) (ξ k - μ x) γ)
    + frob Y (η • Sig x - outerDev ξ μ x k)) ≤ _ at hk
  rw [hZb, frob_block2, frob_comm Y, frob_smul_sub, frob_comm z1, dotProduct_sub,
    dotProduct_comm z2 (μ x)] at hk
  linarith

end

section

open DDMomentDRO.Type3 in
open Matrix in
theorem solution {I J K : ℕ} (S : Set ((Fin I → ℝ) × (Fin I → Fin J → ℝ)))
    (g : (Fin I → ℝ) → (Fin I → Fin J → ℝ) → ℝ) (ξ : Fin K → Fin J → ℝ)
    (Qn : (Fin I → ℝ) → Fin K → ℝ) (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ η : ℝ)
    (hbin : ∀ p ∈ S, ∀ i, p.1 i = 0 ∨ p.1 i = 1)
    (hSig : ∀ x y, (x, y) ∈ S → (Sig x).PosDef)
    (hslater : ∀ x y, (x, y) ∈ S → ∃ p : Fin K → ℝ, IsSlaterPoint ξ μ Sig γ η x p) :
    ∀ q : ℝ, IsLeast (stageVals S g Qn ξ μ Sig γ η) q ↔
      IsLeast (dualVals3 S g Qn ξ μ Sig γ η) q := by
  intro q
  have key := isLeast_add_isGreatest_iff S (fun xy => g xy.1 xy.2)
    (fun xy => wcVal Qn ξ μ Sig γ η xy.1)
    (fun xy => {d | ∃ s z1 z2 z3 Y, DualFeas3 Qn ξ μ xy.1 s z1 z2 z3 Y ∧
      d = dualObj3 μ Sig γ η xy.1 s z1 z2 z3 Y})
    (fun xy hxy => strong Qn ξ μ Sig γ η xy.1
      (hSig xy.1 xy.2 hxy) (hslater xy.1 xy.2 hxy)) q
  have e1 : stageVals S g Qn ξ μ Sig γ η = {v | ∃ xy ∈ S, ∃ w,
      IsGreatest (wcVal Qn ξ μ Sig γ η xy.1) w ∧ v = g xy.1 xy.2 + w} := by
    ext v; constructor
    · rintro ⟨x, y, w, hS, hw, rfl⟩; exact ⟨(x, y), hS, w, hw, rfl⟩
    · rintro ⟨⟨x, y⟩, hS, w, hw, rfl⟩; exact ⟨x, y, w, hS, hw, rfl⟩
  have e2 : dualVals3 S g Qn ξ μ Sig γ η = {v | ∃ xy ∈ S, ∃ d ∈ {d | ∃ s z1 z2 z3 Y,
      DualFeas3 Qn ξ μ xy.1 s z1 z2 z3 Y ∧ d = dualObj3 μ Sig γ η xy.1 s z1 z2 z3 Y},
      v = g xy.1 xy.2 + d} := by
    ext v; constructor
    · rintro ⟨x, y, s, z1, z2, z3, Y, hS, hD, rfl⟩
      exact ⟨(x, y), hS, _, ⟨s, z1, z2, z3, Y, hD, rfl⟩, rfl⟩
    · rintro ⟨⟨x, y⟩, hS, d, ⟨s, z1, z2, z3, Y, hD, rfl⟩, rfl⟩
      exact ⟨x, y, s, z1, z2, z3, Y, hS, hD, rfl⟩
  rw [e1, e2]
  exact key

end
