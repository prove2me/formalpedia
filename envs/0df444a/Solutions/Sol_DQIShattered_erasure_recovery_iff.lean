-- Prove2me | solution 1 for DQIShattered.erasure_recovery_iff
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-25T05:06:22.500807+00:00
-- url     : https://prove2.me/submissions/15562ddb-b2c7-433a-b048-a38ea1bb32b9

import Mathlib
import Definitions.Def_DQIShattered_Decoding

open DQIShattered

/-! The intermediate property: the only codeword of `C^⊥` vanishing off `S` is `0`
(the kernel of the erasure-restricted parity system is trivial, i.e. Gaussian
elimination has a unique solution). -/
abbrev KernelUniqueOffS {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (S : Finset (Fin M)) : Prop :=
  ∀ e : Reg M, (∀ j, j ∉ S → e j = 0) → B.transpose.mulVec e = 0 → e = 0

namespace P2MHole01_20d771db
theorem solution {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod (2 : ℕ))) (S : Finset (Fin M)) :
  (∀ d ∈ dualCode B, ∀ d' ∈ dualCode B, (∀ j ∉ S, d j = d' j) → d = d') → KernelUniqueOffS B S := by
  intro H e hE hB
  have h_zero : (0 : Reg M) ∈ dualCode B := by
    simp only [dualCode, Finset.mem_filter]
    constructor
    · simp
    · ext j
      simp [Matrix.mulVec]
  have h_e : e ∈ dualCode B := by
    simp only [dualCode, Finset.mem_filter]
    constructor
    · simp
    · exact hB
  have hAgree : ∀ j ∉ S, e j = (0 : Reg M) j := by
    intro j hj
    rw [hE j hj]
    rfl
  exact H e h_e 0 h_zero hAgree
end P2MHole01_20d771db

-- L1 — recovery ⇒ KU: if any two codewords that agree off `S` are equal, then the
-- only codeword vanishing off `S` is `0` (take the two codewords `0` and `e`).
lemma recovery_implies_kernel_unique {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (S : Finset (Fin M)) :
    (∀ d ∈ dualCode B, ∀ d' ∈ dualCode B, (∀ j, j ∉ S → d j = d' j) → d = d') →
    KernelUniqueOffS B S := by (first | exact P2MHole01_20d771db.solution B S | (apply P2MHole01_20d771db.solution <;> assumption))

namespace P2MHole02_e31dd9d0
theorem solution {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod (2 : ℕ))) (S : Finset (Fin M)) :
  KernelUniqueOffS B S → ∀ d ∈ dualCode B, ∀ d' ∈ dualCode B, (∀ j ∉ S, d j = d' j) → d = d' := by
  intro hku d hd d' hd' hagree
  have hd0 : B.transpose.mulVec d = 0 := by simpa [dualCode, Finset.mem_filter] using hd
  have hd'0 : B.transpose.mulVec d' = 0 := by simpa [dualCode, Finset.mem_filter] using hd'
  have hzero : B.transpose.mulVec (d - d') = 0 := by
    rw [Matrix.mulVec_sub]
    simpa [hd0, hd'0]
  have hvanish : ∀ j, j ∉ S → (d - d') j = 0 := by
    intro j hj
    change d j - d' j = 0
    exact sub_eq_zero.2 (hagree j hj)
  rw [← sub_eq_zero]
  exact hku (d - d') hvanish hzero
end P2MHole02_e31dd9d0

-- L2 — KU ⇒ recovery: if the only codeword vanishing off `S` is `0`, then any two
-- codewords agreeing off `S` are equal (their difference vanishes off `S`).
lemma kernel_unique_implies_recovery {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (S : Finset (Fin M)) :
    KernelUniqueOffS B S →
    (∀ d ∈ dualCode B, ∀ d' ∈ dualCode B, (∀ j, j ∉ S → d j = d' j) → d = d') := by (first | exact P2MHole02_e31dd9d0.solution B S | (apply P2MHole02_e31dd9d0.solution <;> assumption))

namespace P2MHole03_dc0e1137
open scoped BigOperators

/-! Given a finitely-supported coefficient `w` on the rows indexed by `S`, the register
`e` obtained by placing `w i` at coordinate `i` (and `0` outside `S`) satisfies
`Bᵀ e = Σ i in w.support, w i • B i`. -/

/- Fintype sum over `Fin M` of a function that is `0` outside `S` = sum over `S`. -/
lemma fintype_sum_finset_zero_outside {M : ℕ} (S : Finset (Fin M)) {α : Type*} [AddCommMonoid α]
    (f : Fin M → α) (hf : ∀ j, j ∉ S → f j = 0) :
    ∑ j : Fin M, f j = ∑ j ∈ S, f j := by
  classical
  have h0 : ∑ j ∈ (Finset.univ : Finset (Fin M)) \ S, f j = 0 := by
    rw [Finset.sum_eq_zero]
    intro j hj
    exact hf j ((Finset.mem_sdiff.mp hj).2)
  have h1 : (∑ j ∈ (Finset.univ : Finset (Fin M)) \ S, f j) + ∑ j ∈ S, f j =
      ∑ j ∈ (Finset.univ : Finset (Fin M)), f j :=
    Finset.sum_sdiff (Finset.subset_univ S)
  calc
    ∑ j : Fin M, f j = ∑ j ∈ (Finset.univ : Finset (Fin M)), f j := rfl
    _ = ∑ j ∈ S, f j := by
      rw [← h1, h0]
      simp

/- Finset sum over `S : Finset (Fin M)` = Fintype sum over the subtype `S`. -/
lemma bridge_finset_subtype {M : ℕ} (S : Finset (Fin M)) {α : Type*} [AddCommMonoid α] (F : Fin M → α) :
    (∑ x ∈ S, F x) = ∑ i : S, F i.1 := by
  classical
  have : ∑ x ∈ S, F x = ∑ i ∈ (Finset.univ : Finset S), F i.1 :=
    Finset.sum_bij (fun x hx => ⟨x, hx⟩)
      (fun x _ => by simp)
      (fun x₁ _ x₂ _ h => congrArg Subtype.val h)
      (fun b _ => ⟨b.1, b.2, Subtype.ext rfl⟩)
      (fun x _ => rfl)
  calc
    _ = ∑ i ∈ (Finset.univ : Finset S), F i.1 := this
    _ = ∑ i : S, F i.1 := rfl

/- Fintype sum over a subtype `S` of `w i * g i` = sum over the support of `w`. -/
lemma fintype_sum_finsupp_zmod {S : Type*} [Fintype S] [DecidableEq S]
    (w : S →₀ ZMod 2) (g : S → ZMod 2) :
    ∑ i : S, w i * g i = ∑ i ∈ w.support, w i * g i := by
  classical
  have hzero : ∑ i ∈ (Finset.univ : Finset S) \ w.support, w i * g i = 0 :=
    Finset.sum_eq_zero fun i (hi : i ∈ (Finset.univ : Finset S) \ w.support) => by
      have hno : i ∉ w.support := (Finset.mem_sdiff.mp hi).2
      have hwi : w i = 0 := by
        rw [Finsupp.mem_support_iff] at hno
        exact not_not.mp hno
      rw [hwi, zero_mul]
  calc
    ∑ i : S, w i * g i = ∑ i ∈ (Finset.univ : Finset S), w i * g i := rfl
    _ = (∑ i ∈ (Finset.univ : Finset S) \ w.support, w i * g i) + ∑ i ∈ w.support, w i * g i :=
        (Finset.sum_sdiff (Finset.subset_univ w.support)).symm
    _ = 0 + ∑ i ∈ w.support, w i * g i := by rw [hzero]
    _ = ∑ i ∈ w.support, w i * g i := by simp

/- The key identity: the parity product `Bᵀ e` of the zero-extended register `e` is the
linear combination of the rows `B i` (`i ∈ S`) with coefficients `w`. -/
theorem lincomb_eq {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (S : Finset (Fin M))
    (w : S →₀ ZMod 2) :
    B.transpose.mulVec (fun j => if h : j ∈ S then w ⟨j, h⟩ else 0) =
    Finsupp.linearCombination (ZMod 2) (fun i : S => B i) w := by
  set e := (fun j => if h : j ∈ S then w ⟨j, h⟩ else 0) with he
  change B.transpose.mulVec e = Finsupp.linearCombination (ZMod 2) (fun i : S => B i) w
  ext x
  simp only [Matrix.mulVec, Matrix.transpose_apply, Finsupp.linearCombination_apply, dotProduct,
    Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hzero : ∀ j, j ∉ S → e j = 0 := by
    intro j hj
    dsimp only [e]
    simp [hj]
  have hw_on : ∀ i : S, e i.1 = w i := by
    intro i
    dsimp only [e]
    simp [i.2]
  calc
    _ = ∑ j ∈ S, B j x * e j :=
        fintype_sum_finset_zero_outside S (fun j => B j x * e j) (fun j hj => by rw [hzero j hj, mul_zero])
    _ = ∑ i : S, B i.1 x * e i.1 :=
        bridge_finset_subtype S (fun j => B j x * e j)
    _ = ∑ i : S, B i.1 x * w i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hw_on i]
    _ = ∑ i : S, w i * B i.1 x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_comm]
    _ = ∑ i ∈ w.support, w i * B i.1 x :=
        fintype_sum_finsupp_zmod w (fun i : S => B i.1 x)

theorem solution {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod (2 : ℕ))) (S : Finset (Fin M)) :
  KernelUniqueOffS B S → FullRowRankOn B S := by
  intro h_unique
  -- `FullRowRankOn B S` is `LinearIndependent (ZMod 2) (fun i : S => B i)`, which by
  -- the injective characterisation of linear independence is
  -- `Function.Injective (Finsupp.linearCombination (ZMod 2) (fun i : S => B i))`.
  unfold FullRowRankOn
  unfold LinearIndependent
  intro w₁ w₂ h
  set w := w₁ - w₂ with hw
  have hcomb : Finsupp.linearCombination (ZMod 2) (fun i : S => B i) w = 0 := by
    rw [hw, map_sub, h, sub_self]
  set e : Reg M := fun j => if hmem : j ∈ S then w ⟨j, hmem⟩ else 0 with he
  have h_off : ∀ j, j ∉ S → e j = 0 := by
    intro j hj
    dsimp only [e]
    simp [hj]
  have h_trans : B.transpose.mulVec e = 0 := by
    rw [lincomb_eq _ _ _, hcomb]
  have h_e0 : e = 0 := h_unique e h_off h_trans
  have hw0 : w = 0 := by
    ext i
    have hi : e i.1 = w i := by
      dsimp only [e]
      simp [i.2]
    rw [← hi, h_e0]
    rfl
  -- `w = 0` means `w₁ - w₂ = 0`, i.e. `w₁ = w₂`.
  rw [hw] at hw0
  rwa [sub_eq_zero] at hw0
end P2MHole03_dc0e1137

-- riskiest
-- L3 — KU ⇒ FullRowRankOn: from a relation `∑ l_i • B i = 0` among the rows indexed
-- by `S`, build `e j = if h : j ∈ S then l ⟨j, h⟩ else 0`, which vanishes off `S`
-- and satisfies `Bᵀ e = 0`; KU then forces the relation to be trivial.
lemma kernel_unique_implies_full_row_rank {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (S : Finset (Fin M)) :
    KernelUniqueOffS B S → FullRowRankOn B S := by (first | exact P2MHole03_dc0e1137.solution B S | (apply P2MHole03_dc0e1137.solution <;> assumption))

namespace P2MHole04_0843ffef
theorem solution {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod (2 : ℕ))) (S : Finset (Fin M)) :
  FullRowRankOn B S → KernelUniqueOffS B S := by
  intro hrank e hsupp hze
  -- (a) the full row sum (over all rows) is exactly the matrix product Bᵀ e
  have hfull : B.transpose.mulVec e = (∑ i : Fin M, e i • B i : Fin N → ZMod 2) := by
    ext k
    dsimp only [Matrix.mulVec]
    simp [dotProduct, Matrix.transpose_apply, mul_comm, smul_eq_mul]
  -- (b) restrict the full sum to S: e vanishes off S, so the sum over S is the full sum
  have hrestrict : (∑ i : S, e i • B i : Fin N → ZMod 2) = ∑ i : Fin M, e i • B i := by
    have h0 : ∀ (i : Fin M), i ∉ Set.range (Subtype.val : S → Fin M) → (fun (i : Fin M) => e i • B i) i = 0 := by
      intro i hi
      have h : i ∉ S := by simpa using hi
      change e i • B i = 0
      rw [hsupp i h, zero_smul]
    exact Fintype.sum_of_injective (Subtype.val : S → Fin M) Subtype.coe_injective
      (fun i => e i • B i) (fun i => e i • B i) h0 (by intro i; rfl)
  -- (c) hence the S-weighted row sum is the zero vector
  have hzero : (∑ i : S, e i • B i : Fin N → ZMod 2) = 0 := by
    rw [hrestrict, ← hfull, hze]
  -- (d) linear independence of the rows indexed by S kills every coefficient on S
  have hell (i : S) : e i = 0 := by
    have hlin := Fintype.linearIndependent_iff.mp hrank
    exact hlin (fun i : S => e i) hzero i
  -- (e) off S, e is 0 by hypothesis; on S, e is 0 by (d)
  ext j
  by_cases hj : j ∈ S
  · exact hell ⟨j, hj⟩
  · exact hsupp j hj
end P2MHole04_0843ffef

-- L4 — FullRowRankOn ⇒ KU: if the rows indexed by `S` are linearly independent, then
-- a codeword `e` vanishing off `S` gives the relation `∑_{i∈S} e_i • B i = 0`, so
-- `e` is `0` on `S` and hence `0` everywhere.
lemma full_row_rank_implies_kernel_unique {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (S : Finset (Fin M)) :
    FullRowRankOn B S → KernelUniqueOffS B S := by (first | exact P2MHole04_0843ffef.solution B S | (apply P2MHole04_0843ffef.solution <;> assumption))

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, §3.2, p.14 (erasure recovery).

For every `B ∈ 𝔽₂^{M×N}` and every erased set `S ⊆ {1, …, M}`: the erased bits `(d_j)_{j∈S}` of a codeword
`d ∈ C^⊥` are uniquely determined by the unerased bits and the parity checks `Bᵀd = 0` (any two codewords that
agree off `S` are equal) if and only if the row-submatrix `B_S` has full row rank (its rows are linearly
independent over `𝔽₂`). -/
theorem solution {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (S : Finset (Fin M)) :
    (∀ d ∈ dualCode B, ∀ d' ∈ dualCode B, (∀ j, j ∉ S → d j = d' j) → d = d') ↔
      FullRowRankOn B S := by
  constructor
  · intro h
    exact kernel_unique_implies_full_row_rank B S (recovery_implies_kernel_unique B S h)
  · intro h
    exact kernel_unique_implies_recovery B S (full_row_rank_implies_kernel_unique B S h)
