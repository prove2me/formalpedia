-- Prove2me | solution 1 for DiscreteConvex.CombinatorialC.theorem_2_16_conjugacy_general_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:41:12.820487+00:00
-- url     : https://prove2.me/submissions/6a0b6ce5-5736-497d-b129-0808f3e6fa6d

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_GenQF
import Definitions.Def_DiscreteConvex_CombinatorialC_ConjugateWT
import Definitions.Def_DiscreteConvex_CombinatorialC_ToEReal2
import Definitions.Def_DiscreteConvex_CombinatorialC_KerMat
import Definitions.Def_DiscreteConvex_CombinatorialC_OrthComp
import Definitions.Def_DiscreteConvex_CombinatorialC_TranslationSubmodularWT
import Definitions.Def_DiscreteConvex_CombinatorialC_MNatExchangeWT

set_option autoImplicit false
open scoped BigOperators
open Classical
open DiscreteConvex.CombinatorialC

namespace GenQFConjugacy

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def bilin (L : Matrix V V ℝ) (p q : V → ℝ) : ℝ :=
  dotProduct p (L.mulVec q)

lemma bilin_symm (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    bilin L p q = bilin L q p := by
  simpa only [hL.eq, bilin] using Matrix.dotProduct_transpose_mulVec L p q

lemma bilin_add_left (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L (p + q) r = bilin L p r + bilin L q r := by
  simp only [bilin, add_dotProduct]

lemma bilin_add_right (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L p (q + r) = bilin L p q + bilin L p r := by
  simp only [bilin, Matrix.mulVec_add, dotProduct_add]

lemma bilin_sub_left (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L (p - q) r = bilin L p r - bilin L q r := by
  simp only [bilin, sub_dotProduct]

lemma bilin_sub_right (L : Matrix V V ℝ) (p q r : V → ℝ) :
    bilin L p (q - r) = bilin L p q - bilin L p r := by
  simp only [bilin, Matrix.mulVec_sub, dotProduct_sub]

lemma bilin_smul_left (L : Matrix V V ℝ) (a : ℝ) (p q : V → ℝ) :
    bilin L (a • p) q = a * bilin L p q := by
  simp only [bilin, smul_dotProduct, smul_eq_mul]

lemma bilin_smul_right (L : Matrix V V ℝ) (a : ℝ) (p q : V → ℝ) :
    bilin L p (a • q) = a * bilin L p q := by
  simp only [bilin, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma bilin_eq_sum (L : Matrix V V ℝ) (p q : V → ℝ) :
    bilin L p q = ∑ i, ∑ j, L i j * (p i * q j) := by
  simp only [bilin, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp] lemma qf_zero (L : Matrix V V ℝ) : QF L (0 : V → ℝ) = 0 := by
  simp [QF]

lemma qf_add (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L (p + q) = QF L p + QF L q + bilin L p q := by
  change (1 / 2 : ℝ) * bilin L (p + q) (p + q) =
    (1 / 2 : ℝ) * bilin L p p + (1 / 2 : ℝ) * bilin L q q + bilin L p q
  simp only [bilin_add_left, bilin_add_right]
  rw [bilin_symm L hL q p]
  ring

lemma qf_sub (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L (p - q) = QF L p + QF L q - bilin L p q := by
  change (1 / 2 : ℝ) * bilin L (p - q) (p - q) =
    (1 / 2 : ℝ) * bilin L p p + (1 / 2 : ℝ) * bilin L q q - bilin L p q
  simp only [bilin_sub_left, bilin_sub_right]
  rw [bilin_symm L hL q p]
  ring

lemma qf_smul (L : Matrix V V ℝ) (a : ℝ) (p : V → ℝ) :
    QF L (a • p) = a ^ 2 * QF L p := by
  change (1 / 2 : ℝ) * bilin L (a • p) (a • p) = a ^ 2 * ((1 / 2 : ℝ) * bilin L p p)
  rw [bilin_smul_left, bilin_smul_right]
  ring

lemma qf_neg (L : Matrix V V ℝ) (p : V → ℝ) :
    QF L (-p) = QF L p := by
  have h : (-p : V → ℝ) = (-1 : ℝ) • p := by ext i; simp
  rw [h, qf_smul]
  ring

lemma qf_exchange (L : Matrix V V ℝ) (hL : L.IsSymm)
    (x y d : V → ℝ) (a : ℝ) :
    QF L (x - a • d) + QF L (y + a • d) =
      QF L x + QF L y - a * bilin L (x - y) d + a ^ 2 * bilin L d d := by
  simp only [qf_sub L hL, qf_add L hL, qf_smul, bilin_smul_right, bilin_sub_left]
  change (QF L x + a ^ 2 * ((1 / 2 : ℝ) * bilin L d d) - a * bilin L x d) +
      (QF L y + a ^ 2 * ((1 / 2 : ℝ) * bilin L d d) + a * bilin L y d) = _
  ring

lemma qf_parallelogram (L : Matrix V V ℝ) (hL : L.IsSymm) (p q : V → ℝ) :
    QF L p + QF L q = (1 / 2 : ℝ) * (QF L (p + q) + QF L (p - q)) := by
  rw [qf_add L hL, qf_sub L hL]
  ring

lemma qf_nonneg (M : Matrix V V ℝ) (hM : M.PosSemidef) (x : V → ℝ) :
    0 ≤ QF M x := by
  unfold QF
  apply mul_nonneg (by norm_num)
  simpa only [star_trivial] using hM.dotProduct_mulVec_nonneg x

lemma bilin_self_eq_two_qf (M : Matrix V V ℝ) (x : V → ℝ) :
    bilin M x x = 2 * QF M x := by
  unfold QF bilin
  ring

lemma quad_linear_eq_zero (a b : ℝ) (h : ∀ t : ℝ, 0 ≤ t * a + t ^ 2 * b) : a = 0 := by
  have hpos : ∀ eps : ℝ, 0 < eps → -eps * b ≤ a ∧ a ≤ eps * b := by
    intro eps heps
    have h1 := h eps
    have h2 := h (-eps)
    constructor <;> nlinarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hb : 0 < |b| + 1 := by positivity
    have heps : 0 < (-a) / (2 * (|b| + 1)) := div_pos (neg_pos.mpr hlt) (by positivity)
    have hle := (hpos _ heps).1
    have hble : b ≤ |b| + 1 := by linarith [le_abs_self b]
    have hmul : ((-a) / (2 * (|b| + 1))) * b ≤ ((-a) / (2 * (|b| + 1))) * (|b| + 1) :=
      mul_le_mul_of_nonneg_left hble heps.le
    have hsimp : ((-a) / (2 * (|b| + 1))) * (|b| + 1) = (-a) / 2 := by
      field_simp
    linarith
  · have hb : 0 < |b| + 1 := by positivity
    have heps : 0 < a / (2 * (|b| + 1)) := div_pos hgt (by positivity)
    have hle := (hpos _ heps).2
    have hble : b ≤ |b| + 1 := by linarith [le_abs_self b]
    have hmul : (a / (2 * (|b| + 1))) * b ≤ (a / (2 * (|b| + 1))) * (|b| + 1) :=
      mul_le_mul_of_nonneg_left hble heps.le
    have hsimp : (a / (2 * (|b| + 1))) * (|b| + 1) = a / 2 := by
      field_simp
    linarith

lemma qf_eq_zero_iff (M : Matrix V V ℝ) (hM : M.IsSymm) (hMpsd : M.PosSemidef) (x : V → ℝ) :
    QF M x = 0 ↔ M.mulVec x = 0 := by
  constructor
  · intro hx
    have hbilin : ∀ y : V → ℝ, bilin M x y = 0 := by
      intro y
      apply quad_linear_eq_zero _ (QF M y)
      intro t
      have h0 := qf_nonneg M hMpsd (x + t • y)
      rw [qf_add M hM, qf_smul, bilin_smul_right, hx, zero_add] at h0
      linarith
    have hself : dotProduct (M.mulVec x) (M.mulVec x) = 0 := by
      have h := hbilin (M.mulVec x)
      rw [bilin_symm M hM] at h
      exact h
    exact dotProduct_self_eq_zero.mp hself
  · intro hx
    simp [QF, hx]

lemma charVec_eq_single (i : V) : CharVec i = Pi.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i <;> simp [CharVec, Pi.single_apply, h]

lemma dot_charVec_left (i : V) (p : V → ℝ) : dotProduct (CharVec i) p = p i := by
  simp [charVec_eq_single]

lemma dot_charVec_right (p : V → ℝ) (i : V) : dotProduct p (CharVec i) = p i := by
  simp [charVec_eq_single]

lemma orthComp_zero (S : Set (V → ℝ)) : (0 : V → ℝ) ∈ OrthComp S := by
  intro x _; simp

lemma orthComp_add {S : Set (V → ℝ)} {p q : V → ℝ} (hp : p ∈ OrthComp S) (hq : q ∈ OrthComp S) :
    p + q ∈ OrthComp S := by
  intro x hx; rw [add_dotProduct, hp x hx, hq x hx, add_zero]

lemma orthComp_sub {S : Set (V → ℝ)} {p q : V → ℝ} (hp : p ∈ OrthComp S) (hq : q ∈ OrthComp S) :
    p - q ∈ OrthComp S := by
  intro x hx; rw [sub_dotProduct, hp x hx, hq x hx, sub_zero]

lemma orthComp_smul {S : Set (V → ℝ)} (a : ℝ) {p : V → ℝ} (hp : p ∈ OrthComp S) :
    a • p ∈ OrthComp S := by
  intro x hx; rw [smul_dotProduct, hp x hx, smul_eq_mul, mul_zero]

lemma orthComp_neg {S : Set (V → ℝ)} {p : V → ℝ} (hp : p ∈ OrthComp S) :
    -p ∈ OrthComp S := by
  intro x hx; rw [neg_dotProduct, hp x hx, neg_zero]

lemma orthComp_sum {S : Set (V → ℝ)} {ι : Type*} (s : Finset ι) (f : ι → V → ℝ)
    (hf : ∀ i ∈ s, f i ∈ OrthComp S) :
    (∑ i ∈ s, f i) ∈ OrthComp S := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp [orthComp_zero]
  · rw [Finset.sum_insert ha]
    exact orthComp_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma mulVec_mem_orthComp_ker (L : Matrix V V ℝ) (hL : L.IsSymm) (A : Set (V → ℝ)) (p : V → ℝ) :
    L.mulVec p ∈ OrthComp (A ∩ KerMat L) := by
  intro q hq
  have h1 : dotProduct (L.mulVec p) q = bilin L q p := by
    rw [dotProduct_comm]; rfl
  rw [h1, bilin_symm L hL]
  change dotProduct p (L.mulVec q) = 0
  rw [hq.2, dotProduct_zero]

lemma orthComp_orthComp_ker_iff (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ))
    (hLsymm : L.IsSymm) (hMsymm : M.IsSymm) (hMpsd : M.PosSemidef)
    (hK : K = OrthComp (Hs ∩ KerMat M)) (hH : Hs = OrthComp (K ∩ KerMat L))
    (z : V → ℝ) :
    z ∈ Hs ∩ KerMat M ↔ z ∈ OrthComp K := by
  constructor
  · intro hz p hp
    rw [hK] at hp
    rw [dotProduct_comm]
    exact hp z hz
  · intro hz
    have hzH : z ∈ Hs := by
      rw [hH]
      intro q hq
      exact hz q hq.1
    have hzM : z ∈ KerMat M := by
      have hMz : M.mulVec z ∈ K := by
        rw [hK]
        exact mulVec_mem_orthComp_ker M hMsymm Hs z
      have h0 : dotProduct z (M.mulVec z) = 0 := hz (M.mulVec z) hMz
      have hqf : QF M z = 0 := by
        unfold QF
        rw [h0, mul_zero]
      exact (qf_eq_zero_iff M hMsymm hMpsd z).mp hqf
    exact ⟨hzH, hzM⟩

lemma fenchel_young (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ))
    (hconj1 : ∀ p : V → ℝ, ConjugateWT (GenQF M Hs) p = ToEReal2 (GenQF L K p))
    {p x : V → ℝ} (hp : p ∈ K) (hx : x ∈ Hs) :
    dotProduct p x ≤ QF L p + QF M x := by
  have hc := hconj1 p
  unfold ConjugateWT at hc
  have hle : ((dotProduct p x : ℝ) : EReal) - ToEReal2 (GenQF M Hs x) ≤
      ToEReal2 (GenQF L K p) := by
    rw [← hc]
    exact le_sSup ⟨x, rfl⟩
  simp only [GenQF, hp, hx, ↓reduceIte, ToEReal2] at hle
  change ((dotProduct p x : ℝ) : EReal) - ((QF M x : ℝ) : EReal) ≤ ((QF L p : ℝ) : EReal) at hle
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hle
  linarith

lemma qf_M_mulVec_L (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ))
    (hLsymm : L.IsSymm) (hLpsd : L.PosSemidef)
    (hH : Hs = OrthComp (K ∩ KerMat L))
    (hconj2 : ∀ x : V → ℝ, ConjugateWT (GenQF L K) x = ToEReal2 (GenQF M Hs x))
    {p : V → ℝ} (hp : p ∈ K) :
    QF M (L.mulVec p) = QF L p := by
  have hLp : L.mulVec p ∈ Hs := by
    rw [hH]
    exact mulVec_mem_orthComp_ker L hLsymm K p
  have hc := hconj2 (L.mulVec p)
  simp only [GenQF, hLp, ↓reduceIte, ToEReal2] at hc
  change ConjugateWT (GenQF L K) (L.mulVec p) = ((QF M (L.mulVec p) : ℝ) : EReal) at hc
  have hmax : ConjugateWT (GenQF L K) (L.mulVec p) = ((QF L p : ℝ) : EReal) := by
    unfold ConjugateWT
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨q, rfl⟩
      by_cases hq : q ∈ K
      · simp only [GenQF, hq, ↓reduceIte, ToEReal2]
        change ((dotProduct (L.mulVec p) q : ℝ) : EReal) - ((QF L q : ℝ) : EReal) ≤
          ((QF L p : ℝ) : EReal)
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        have hsub := qf_sub L hLsymm p q
        have hnn := qf_nonneg L hLpsd (p - q)
        have hbil : dotProduct (L.mulVec p) q = bilin L p q := by
          rw [dotProduct_comm, ← bilin_symm L hLsymm]; rfl
        linarith
      · simp only [GenQF, hq, ↓reduceIte, ToEReal2]
        change ((dotProduct (L.mulVec p) q : ℝ) : EReal) - (⊤ : EReal) ≤ ((QF L p : ℝ) : EReal)
        simp
    · apply le_sSup
      refine ⟨p, ?_⟩
      simp only [GenQF, hp, ↓reduceIte, ToEReal2]
      change ((QF L p : ℝ) : EReal) =
        ((dotProduct (L.mulVec p) p : ℝ) : EReal) - ((QF L p : ℝ) : EReal)
      rw [← EReal.coe_sub, EReal.coe_eq_coe_iff]
      have hbil : dotProduct (L.mulVec p) p = 2 * QF L p := by
        rw [dotProduct_comm]; exact bilin_self_eq_two_qf L p
      linarith
  exact EReal.coe_eq_coe_iff.mp (hc.symm.trans hmax)

lemma sub_mulVec_M_mulVec_L_mem (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ))
    (hLsymm : L.IsSymm) (hMsymm : M.IsSymm) (hLpsd : L.PosSemidef) (hMpsd : M.PosSemidef)
    (hK : K = OrthComp (Hs ∩ KerMat M)) (hH : Hs = OrthComp (K ∩ KerMat L))
    (hconj : (∀ p : V → ℝ, ConjugateWT (GenQF M Hs) p = ToEReal2 (GenQF L K p)) ∧
      (∀ x : V → ℝ, ConjugateWT (GenQF L K) x = ToEReal2 (GenQF M Hs x)))
    {p : V → ℝ} (hp : p ∈ K) :
    p - M.mulVec (L.mulVec p) ∈ K ∩ KerMat L := by
  rw [orthComp_orthComp_ker_iff M L Hs K hMsymm hLsymm hLpsd hH hK]
  intro y hy
  have hLp : L.mulVec p ∈ Hs := by
    rw [hH]; exact mulVec_mem_orthComp_ker L hLsymm K p
  have hq : QF M (L.mulVec p) = QF L p :=
    qf_M_mulVec_L L M K Hs hLsymm hLpsd hH hconj.2 hp
  apply quad_linear_eq_zero _ (QF M y)
  intro t
  have hty : L.mulVec p + (-t) • y ∈ Hs := by
    rw [hH] at hLp hy ⊢
    exact orthComp_add hLp (orthComp_smul (-t) hy)
  have hfy := fenchel_young L M K Hs hconj.1 hp hty
  rw [qf_add M hMsymm, qf_smul, bilin_smul_right, hq] at hfy
  have htsq : (-t) ^ 2 = t ^ 2 := by ring
  have hdot : dotProduct p (L.mulVec p + (-t) • y) =
      2 * QF L p - t * dotProduct p y := by
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, ← bilin_self_eq_two_qf L p]
    unfold bilin
    ring
  have hbil : bilin M (L.mulVec p) y = dotProduct y (M.mulVec (L.mulVec p)) := by
    rw [bilin_symm M hMsymm]; rfl
  have hsub : dotProduct (p - M.mulVec (L.mulVec p)) y =
      dotProduct p y - dotProduct y (M.mulVec (L.mulVec p)) := by
    rw [sub_dotProduct, dotProduct_comm (M.mulVec (L.mulVec p)) y]
  rw [htsq, hdot, hbil] at hfy
  rw [hsub]
  linarith

lemma dotProduct_mulVec_M_mulVec_L_eq (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ))
    (hLsymm : L.IsSymm) (hMsymm : M.IsSymm) (hLpsd : L.PosSemidef) (hMpsd : M.PosSemidef)
    (hK : K = OrthComp (Hs ∩ KerMat M)) (hH : Hs = OrthComp (K ∩ KerMat L))
    (hconj : (∀ p : V → ℝ, ConjugateWT (GenQF M Hs) p = ToEReal2 (GenQF L K p)) ∧
      (∀ x : V → ℝ, ConjugateWT (GenQF L K) x = ToEReal2 (GenQF M Hs x)))
    {p d : V → ℝ} (hp : p ∈ K) (hd : d ∈ Hs) :
    dotProduct d (M.mulVec (L.mulVec p)) = dotProduct d p := by
  have hmem := sub_mulVec_M_mulVec_L_mem L M K Hs hLsymm hMsymm hLpsd hMpsd hK hH hconj hp
  rw [hH] at hd
  have h0 : dotProduct d (p - M.mulVec (L.mulVec p)) = 0 := hd _ hmem
  rw [dotProduct_sub] at h0
  linarith

/-! ### Step A: `MNatExchangeWT (GenQF M Hs) ↔ CondCPlusGen M Hs` -/

def CondCPlusGen (M : Matrix V V ℝ) (Hs : Set (V → ℝ)) : Prop :=
  ∀ z ∈ Hs, ∀ i ∈ SuppPosR z,
    (∃ j ∈ SuppNegR z, CharVec i - CharVec j ∈ Hs ∧
      (CharVec i - CharVec j ∈ KerMat M ∨ (M.mulVec z) j < (M.mulVec z) i)) ∨
    (CharVec i ∈ Hs ∧ (CharVec i ∈ KerMat M ∨ 0 < (M.mulVec z) i))

lemma genQF_ne_top_iff (M : Matrix V V ℝ) (Hs : Set (V → ℝ)) (x : V → ℝ) :
    GenQF M Hs x ≠ ⊤ ↔ x ∈ Hs := by
  unfold GenQF
  split_ifs with hx
  · simp [hx]
  · simp [hx]

lemma genQF_exchange_interval_iff (M : Matrix V V ℝ) (Hs : Set (V → ℝ))
    (hMsymm : M.IsSymm) (hMpsd : M.PosSemidef) (A : Set (V → ℝ)) (hH : Hs = OrthComp A)
    {x y : V → ℝ} (hx : x ∈ Hs) (hy : y ∈ Hs) (d : V → ℝ) :
    (∃ a0 : ℝ, 0 < a0 ∧ ∀ a : ℝ, 0 ≤ a → a ≤ a0 →
      GenQF M Hs x + GenQF M Hs y ≥ GenQF M Hs (x - a • d) + GenQF M Hs (y + a • d)) ↔
      d ∈ Hs ∧ (d ∈ KerMat M ∨ 0 < bilin M (x - y) d) := by
  constructor
  · rintro ⟨a0, ha0, h⟩
    have h1 := h a0 ha0.le le_rfl
    have hxy : GenQF M Hs x + GenQF M Hs y ≠ ⊤ := by
      simp [GenQF, hx, hy, ← WithTop.coe_add]
    have hsub_ne : GenQF M Hs (x - a0 • d) ≠ ⊤ := by
      intro htop
      rw [htop, top_add, ge_iff_le, top_le_iff] at h1
      exact hxy h1
    have hxd : x - a0 • d ∈ Hs := (genQF_ne_top_iff M Hs _).mp hsub_ne
    have hd : d ∈ Hs := by
      have hdiff : x - (x - a0 • d) ∈ Hs := by
        rw [hH] at hx hxd ⊢
        exact orthComp_sub hx hxd
      have heq : d = (1 / a0) • (x - (x - a0 • d)) := by
        ext k; simp [ha0.ne']
      rw [heq, hH]
      rw [hH] at hdiff
      exact orthComp_smul (1 / a0) hdiff
    refine ⟨hd, ?_⟩
    by_cases hker : d ∈ KerMat M
    · exact Or.inl hker
    · right
      have hqf_ne : QF M d ≠ 0 := fun h0 => hker ((qf_eq_zero_iff M hMsymm hMpsd d).mp h0)
      have hqf_pos : 0 < QF M d := lt_of_le_of_ne (qf_nonneg M hMpsd d) (Ne.symm hqf_ne)
      have hb_pos : 0 < bilin M d d := by
        rw [bilin_self_eq_two_qf]; linarith
      have hxd' : x - a0 • d ∈ Hs := by
        rw [hH] at hx hd ⊢; exact orthComp_sub hx (orthComp_smul a0 hd)
      have hyd' : y + a0 • d ∈ Hs := by
        rw [hH] at hy hd ⊢; exact orthComp_add hy (orthComp_smul a0 hd)
      simp only [GenQF, hx, hy, hxd', hyd', ↓reduceIte, ge_iff_le,
        ← WithTop.coe_add, WithTop.coe_le_coe] at h1
      rw [qf_exchange M hMsymm] at h1
      by_contra hn
      have hn' : bilin M (x - y) d ≤ 0 := le_of_not_gt hn
      have hlin : a0 * bilin M (x - y) d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0.le hn'
      have hquad : 0 < a0 ^ 2 * bilin M d d := mul_pos (sq_pos_of_pos ha0) hb_pos
      linarith
  · rintro ⟨hd, hker | hpos⟩
    · refine ⟨1, zero_lt_one, fun a _ _ => ?_⟩
      have hxd : x - a • d ∈ Hs := by
        rw [hH] at hx hd ⊢; exact orthComp_sub hx (orthComp_smul a hd)
      have hyd : y + a • d ∈ Hs := by
        rw [hH] at hy hd ⊢; exact orthComp_add hy (orthComp_smul a hd)
      simp only [GenQF, hx, hy, hxd, hyd, ↓reduceIte, ge_iff_le,
        ← WithTop.coe_add, WithTop.coe_le_coe]
      rw [qf_exchange M hMsymm]
      have hbil1 : bilin M (x - y) d = 0 := by simp [bilin, (show M.mulVec d = 0 from hker)]
      have hbil2 : bilin M d d = 0 := by simp [bilin, (show M.mulVec d = 0 from hker)]
      rw [hbil1, hbil2]
      linarith
    · by_cases hker : d ∈ KerMat M
      · have hbil1 : bilin M (x - y) d = 0 := by simp [bilin, (show M.mulVec d = 0 from hker)]
        linarith
      · have hqf_ne : QF M d ≠ 0 := fun h0 => hker ((qf_eq_zero_iff M hMsymm hMpsd d).mp h0)
        have hqf_pos : 0 < QF M d := lt_of_le_of_ne (qf_nonneg M hMpsd d) (Ne.symm hqf_ne)
        have hb : 0 < bilin M d d := by rw [bilin_self_eq_two_qf]; linarith
        refine ⟨bilin M (x - y) d / bilin M d d, div_pos hpos hb, fun a ha0 ha1 => ?_⟩
        have hxd : x - a • d ∈ Hs := by
          rw [hH] at hx hd ⊢; exact orthComp_sub hx (orthComp_smul a hd)
        have hyd : y + a • d ∈ Hs := by
          rw [hH] at hy hd ⊢; exact orthComp_add hy (orthComp_smul a hd)
        simp only [GenQF, hx, hy, hxd, hyd, ↓reduceIte, ge_iff_le,
          ← WithTop.coe_add, WithTop.coe_le_coe]
        rw [qf_exchange M hMsymm]
        have hab : a * bilin M d d ≤ bilin M (x - y) d := (le_div_iff₀ hb).mp ha1
        have he := mul_le_mul_of_nonneg_left hab ha0
        nlinarith

lemma mnatExchangeWT_iff_condCPlusGen (M : Matrix V V ℝ) (Hs : Set (V → ℝ))
    (hMsymm : M.IsSymm) (hMpsd : M.PosSemidef) (A : Set (V → ℝ)) (hH : Hs = OrthComp A) :
    MNatExchangeWT (GenQF M Hs) ↔ CondCPlusGen M Hs := by
  have h0 : (0 : V → ℝ) ∈ Hs := by rw [hH]; exact orthComp_zero A
  constructor
  · intro hExc z hz i hi
    have hz_ne : GenQF M Hs z ≠ ⊤ := (genQF_ne_top_iff M Hs z).mpr hz
    have h0_ne : GenQF M Hs 0 ≠ ⊤ := (genQF_ne_top_iff M Hs 0).mpr h0
    rcases hExc z 0 hz_ne h0_ne i (by simpa only [sub_zero] using hi) with ⟨j, hj, he⟩ | he
    · left
      have hj' : j ∈ SuppNegR z := by simpa only [sub_zero] using hj
      rw [genQF_exchange_interval_iff M Hs hMsymm hMpsd A hH hz h0] at he
      obtain ⟨hdH, hker | hpos⟩ := he
      · exact ⟨j, hj', hdH, Or.inl hker⟩
      · refine ⟨j, hj', hdH, Or.inr ?_⟩
        rw [sub_zero, bilin_symm M hMsymm, bilin, sub_dotProduct,
          dot_charVec_left, dot_charVec_left] at hpos
        linarith
    · right
      rw [genQF_exchange_interval_iff M Hs hMsymm hMpsd A hH hz h0] at he
      obtain ⟨hdH, hker | hpos⟩ := he
      · exact ⟨hdH, Or.inl hker⟩
      · refine ⟨hdH, Or.inr ?_⟩
        rw [sub_zero, bilin_symm M hMsymm, bilin, dot_charVec_left] at hpos
        exact hpos
  · intro hC x y hx_ne hy_ne i hi
    have hx : x ∈ Hs := (genQF_ne_top_iff M Hs x).mp hx_ne
    have hy : y ∈ Hs := (genQF_ne_top_iff M Hs y).mp hy_ne
    have hxy : x - y ∈ Hs := by rw [hH] at hx hy ⊢; exact orthComp_sub hx hy
    rcases hC (x - y) hxy i hi with ⟨j, hj, hdH, hker | hlt⟩ | ⟨hdH, hker | hpos⟩
    · left
      refine ⟨j, hj, ?_⟩
      rw [genQF_exchange_interval_iff M Hs hMsymm hMpsd A hH hx hy]
      exact ⟨hdH, Or.inl hker⟩
    · left
      refine ⟨j, hj, ?_⟩
      rw [genQF_exchange_interval_iff M Hs hMsymm hMpsd A hH hx hy]
      refine ⟨hdH, ?_⟩
      right
      rw [bilin_symm M hMsymm, bilin, sub_dotProduct, dot_charVec_left, dot_charVec_left]
      linarith
    · right
      rw [genQF_exchange_interval_iff M Hs hMsymm hMpsd A hH hx hy]
      exact ⟨hdH, Or.inl hker⟩
    · right
      rw [genQF_exchange_interval_iff M Hs hMsymm hMpsd A hH hx hy]
      refine ⟨hdH, Or.inr ?_⟩
      rw [bilin_symm M hMsymm, bilin, dot_charVec_left]
      exact hpos

/-! ### Step B: Shift-Closed Subspaces, Equivalence Classes, and Support Reduction -/

def upperShift (p q : V → ℝ) (a : ℝ) : V → ℝ :=
  (p - a • (fun _ => (1 : ℝ))) ⊔ q

def lowerShift (p q : V → ℝ) (a : ℝ) : V → ℝ :=
  p ⊓ (q + a • (fun _ => (1 : ℝ)))

def ShiftClosed (S : Set (V → ℝ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ a : ℝ, 0 ≤ a → upperShift p q a ∈ S ∧ lowerShift p q a ∈ S

lemma shiftClosed_of_translationSubmodularWT (L : Matrix V V ℝ) (K : Set (V → ℝ))
    (hSub : TranslationSubmodularWT (GenQF L K)) :
    ShiftClosed K ∧ ∀ p ∈ K, ∀ q ∈ K, ∀ a : ℝ, 0 ≤ a →
      QF L (upperShift p q a) + QF L (lowerShift p q a) ≤ QF L p + QF L q := by
  have h1 : ∀ p ∈ K, ∀ q ∈ K, ∀ a : ℝ, 0 ≤ a →
      (upperShift p q a ∈ K ∧ lowerShift p q a ∈ K) ∧
      QF L (upperShift p q a) + QF L (lowerShift p q a) ≤ QF L p + QF L q := by
    intro p hp q hq a ha
    have hineq := hSub p q a ha
    change GenQF L K p + GenQF L K q ≥
      GenQF L K (upperShift p q a) + GenQF L K (lowerShift p q a) at hineq
    have hpq_ne : GenQF L K p + GenQF L K q ≠ ⊤ := by
      simp [GenQF, hp, hq, ← WithTop.coe_add]
    have hu_ne : GenQF L K (upperShift p q a) ≠ ⊤ := by
      intro htop
      rw [htop, top_add, ge_iff_le, top_le_iff] at hineq
      exact hpq_ne hineq
    have hv_ne : GenQF L K (lowerShift p q a) ≠ ⊤ := by
      intro htop
      rw [htop, add_top, ge_iff_le, top_le_iff] at hineq
      exact hpq_ne hineq
    have hu : upperShift p q a ∈ K := (genQF_ne_top_iff L K _).mp hu_ne
    have hv : lowerShift p q a ∈ K := (genQF_ne_top_iff L K _).mp hv_ne
    simp only [GenQF, hp, hq, hu, hv, ↓reduceIte, ge_iff_le,
      ← WithTop.coe_add, WithTop.coe_le_coe] at hineq
    exact ⟨⟨hu, hv⟩, hineq⟩
  exact ⟨fun p hp q hq a ha => (h1 p hp q hq a ha).1,
    fun p hp q hq a ha => (h1 p hp q hq a ha).2⟩

lemma shiftClosed_ker_inter (L : Matrix V V ℝ) (K : Set (V → ℝ))
    (hLsymm : L.IsSymm) (hLpsd : L.PosSemidef)
    (hSub : TranslationSubmodularWT (GenQF L K)) :
    ShiftClosed (K ∩ KerMat L) := by
  obtain ⟨hK, hineq⟩ := shiftClosed_of_translationSubmodularWT L K hSub
  intro p hp q hq a ha
  obtain ⟨huK, hvK⟩ := hK p hp.1 q hq.1 a ha
  have hle := hineq p hp.1 q hq.1 a ha
  have hp0 : QF L p = 0 := (qf_eq_zero_iff L hLsymm hLpsd p).mpr hp.2
  have hq0 : QF L q = 0 := (qf_eq_zero_iff L hLsymm hLpsd q).mpr hq.2
  have hu_nn := qf_nonneg L hLpsd (upperShift p q a)
  have hv_nn := qf_nonneg L hLpsd (lowerShift p q a)
  have hu0 : QF L (upperShift p q a) = 0 := by linarith
  have hv0 : QF L (lowerShift p q a) = 0 := by linarith
  exact ⟨⟨huK, (qf_eq_zero_iff L hLsymm hLpsd _).mp hu0⟩,
    ⟨hvK, (qf_eq_zero_iff L hLsymm hLpsd _).mp hv0⟩⟩

noncomputable def suppCard (x : V → ℝ) : ℕ :=
  (Finset.univ.filter (fun k => x k ≠ 0)).card

lemma suppCard_eq_zero_iff (x : V → ℝ) : suppCard x = 0 ↔ x = 0 := by
  unfold suppCard
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp [funext_iff]

lemma suppCard_sub_charVec_lt (x : V → ℝ) (i : V) (hx : x i ≠ 0) :
    suppCard (x - x i • CharVec i) < suppCard x := by
  unfold suppCard
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hx⟩, ?_⟩
    simp [CharVec]
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨Finset.mem_univ k, ?_⟩
    intro hxk
    apply hk.2
    by_cases hki : k = i
    · subst k; simp [CharVec]
    · simp [CharVec, hki, hxk]

lemma suppCard_sub_charVec_sub_lt (x : V → ℝ) (i j : V)
    (hi : 0 < x i) (hj : x j < 0) :
    suppCard (if |x i| ≤ |x j| then x - x i • (CharVec i - CharVec j)
      else x + x j • (CharVec i - CharVec j)) < suppCard x := by
  have hij : i ≠ j := by intro h; subst j; linarith
  have hxi : |x i| = x i := abs_of_pos hi
  have hxj : |x j| = -x j := abs_of_neg hj
  split_ifs with hle
  · unfold suppCard
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi.ne'⟩, ?_⟩
      rw [Finset.mem_filter]
      simp [CharVec, hij]
    · intro k hk
      rw [Finset.mem_filter] at hk ⊢
      refine ⟨Finset.mem_univ k, ?_⟩
      intro hxk
      apply hk.2
      have hne1 : k ≠ i := by
        intro h; subst k; exact hi.ne' hxk
      have hne2 : k ≠ j := by
        intro h; subst k; exact hj.ne hxk
      simp [CharVec, hne1, hne2, hxk]
  · unfold suppCard
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj.ne⟩, ?_⟩
      rw [Finset.mem_filter]
      simp [CharVec, hij.symm]
    · intro k hk
      rw [Finset.mem_filter] at hk ⊢
      refine ⟨Finset.mem_univ k, ?_⟩
      intro hxk
      apply hk.2
      have hne1 : k ≠ i := by
        intro h; subst k; exact hi.ne' hxk
      have hne2 : k ≠ j := by
        intro h; subst k; exact hj.ne hxk
      simp [CharVec, hne1, hne2, hxk]

lemma orth_of_charVec_orth (A : Set (V → ℝ))
    (hB : ∀ z ∈ OrthComp A, ∀ i ∈ SuppPosR z,
      CharVec i ∈ OrthComp A ∨ ∃ j ∈ SuppNegR z, CharVec i - CharVec j ∈ OrthComp A)
    (u : V → ℝ)
    (h1 : ∀ i : V, CharVec i ∈ OrthComp A → u i = 0)
    (h2 : ∀ i j : V, CharVec i - CharVec j ∈ OrthComp A → u i = u j) :
    u ∈ OrthComp (OrthComp A) := by
  have hmain : ∀ n : ℕ, ∀ z : V → ℝ, suppCard z = n → z ∈ OrthComp A → dotProduct u z = 0 := by
    intro n
    induction' n using Nat.strong_induction_on with n ih
    intro z hn hz
    by_cases hz0 : z = 0
    · subst z; simp
    · have hex : ∃ i : V, z i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hz0 (funext h)
      obtain ⟨i₀, hi₀⟩ := hex
      have hex_pos : ∃ z' : V → ℝ, (z' = z ∨ z' = -z) ∧ z' ∈ OrthComp A ∧
          suppCard z' = n ∧ ∃ i : V, 0 < z' i := by
        rcases lt_or_gt_of_ne hi₀ with hlt | hgt
        · refine ⟨-z, Or.inr rfl, orthComp_neg hz, ?_, i₀, by simp [hlt]⟩
          rw [← hn]
          unfold suppCard
          congr 1; ext k; simp
        · exact ⟨z, Or.inl rfl, hz, hn, i₀, hgt⟩
      obtain ⟨z', hz'eq, hz'A, hz'n, i, hi⟩ := hex_pos
      suffices hdot' : dotProduct u z' = 0 by
        rcases hz'eq with rfl | rfl
        · exact hdot'
        · rw [dotProduct_neg, neg_eq_zero] at hdot'
          exact hdot'
      have hi_pos : i ∈ SuppPosR z' := by simpa [SuppPosR] using hi
      rcases hB z' hz'A i hi_pos with hci | ⟨j, hj_neg, hcij⟩
      · let w := z' - z' i • CharVec i
        have hwA : w ∈ OrthComp A := orthComp_sub hz'A (orthComp_smul (z' i) hci)
        have hlt : suppCard w < n := by
          rw [← hz'n]
          exact suppCard_sub_charVec_lt z' i hi.ne'
        have ihw := ih (suppCard w) hlt w rfl hwA
        have hui : u i = 0 := h1 i hci
        have hdot_w : dotProduct u w = dotProduct u z' - z' i * u i := by
          simp [w, dotProduct_sub, dotProduct_smul, dot_charVec_right]
        rw [hui, mul_zero, sub_zero] at hdot_w
        linarith
      · have hj : z' j < 0 := by simpa [SuppNegR] using hj_neg
        let w := if |z' i| ≤ |z' j| then z' - z' i • (CharVec i - CharVec j)
          else z' + z' j • (CharVec i - CharVec j)
        have hwA : w ∈ OrthComp A := by
          dsimp [w]
          split_ifs
          · exact orthComp_sub hz'A (orthComp_smul (z' i) hcij)
          · exact orthComp_add hz'A (orthComp_smul (z' j) hcij)
        have hlt : suppCard w < n := by
          rw [← hz'n]
          exact suppCard_sub_charVec_sub_lt z' i j hi hj
        have ihw := ih (suppCard w) hlt w rfl hwA
        have huij : u i = u j := h2 i j hcij
        have hdot_ij : dotProduct u (CharVec i - CharVec j) = 0 := by
          rw [dotProduct_sub, dot_charVec_right, dot_charVec_right, huij, sub_self]
        have hdot_w : dotProduct u w = dotProduct u z' := by
          dsimp [w]
          split_ifs <;> simp [dotProduct_sub, dotProduct_add, dotProduct_smul, hdot_ij]
        linarith
  intro z hz
  exact hmain (suppCard z) z rfl hz

noncomputable def classVec (S : Set (V → ℝ)) (i : V) : V → ℝ :=
  fun k => if ∀ r ∈ S, r k = r i then 1 else 0

lemma classVec_self (S : Set (V → ℝ)) (i : V) : classVec S i i = 1 := by
  simp [classVec]

lemma classVec_nonneg (S : Set (V → ℝ)) (i k : V) : 0 ≤ classVec S i k := by
  unfold classVec; split_ifs <;> norm_num

lemma classVec_le_one (S : Set (V → ℝ)) (i k : V) : classVec S i k ≤ 1 := by
  unfold classVec; split_ifs <;> norm_num

lemma classVec_mem_of_shiftClosed (A : Set (V → ℝ)) (hShift : ShiftClosed (OrthComp A))
    (i : V) (hi : ∃ r₀ ∈ OrthComp A, r₀ i ≠ 0) :
    classVec (OrthComp A) i ∈ OrthComp A := by
  classical
  let S := OrthComp A
  obtain ⟨r₀, hr₀S, hr₀i⟩ := hi
  let absR₀ := upperShift r₀ (-r₀) 0
  have habsR₀ : absR₀ ∈ S := (hShift r₀ hr₀S (-r₀) (orthComp_neg hr₀S) 0 le_rfl).1
  have habsR₀_eq : ∀ k, absR₀ k = |r₀ k| := by
    intro k; simp [absR₀, upperShift, abs_eq_max_neg]
  let s₀ := (1 / |r₀ i|) • absR₀
  have hs₀ : s₀ ∈ S := orthComp_smul (1 / |r₀ i|) habsR₀
  let q₁ := lowerShift s₀ 0 1
  have hq₁ : q₁ ∈ S := (hShift s₀ hs₀ 0 (orthComp_zero A) 1 zero_le_one).2
  have hq₁_nonneg : ∀ k, 0 ≤ q₁ k := by
    intro k
    simp only [q₁, lowerShift, Pi.inf_apply, Pi.add_apply, Pi.zero_apply, Pi.smul_apply,
      smul_eq_mul, mul_one, zero_add, le_inf_iff]
    refine ⟨?_, zero_le_one⟩
    simp only [s₀, Pi.smul_apply, smul_eq_mul, habsR₀_eq]
    positivity
  have hq₁_le_one : ∀ k, q₁ k ≤ 1 := by
    intro k
    simp [q₁, lowerShift]
  have hq₁_i : q₁ i = 1 := by
    simp only [q₁, lowerShift, Pi.inf_apply, Pi.add_apply, Pi.zero_apply, Pi.smul_apply,
      smul_eq_mul, mul_one, zero_add, s₀, habsR₀_eq]
    have hpos : |r₀ i| ≠ 0 := abs_ne_zero.mpr hr₀i
    rw [one_div_mul_cancel hpos, min_self]
  let Bad : Finset V := Finset.univ.filter (fun k => ¬ ∀ r ∈ S, r k = r i)
  have hBad_ex : ∀ k ∈ Bad, ∃ r ∈ S, r k ≠ r i := by
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    push_neg at hk'
    exact hk'
  let rOf (k : V) : V → ℝ :=
    if hk : k ∈ Bad then Classical.choose (hBad_ex k hk) else 0
  have hrOf_mem : ∀ k ∈ Bad, rOf k ∈ S := by
    intro k hk
    simp only [rOf, dif_pos hk]
    exact (Classical.choose_spec (hBad_ex k hk)).1
  have hrOf_ne : ∀ k ∈ Bad, rOf k k ≠ rOf k i := by
    intro k hk
    simp only [rOf, dif_pos hk]
    exact (Classical.choose_spec (hBad_ex k hk)).2
  let wOf (k : V) : V → ℝ := rOf k - (rOf k i) • q₁
  let dOf (k : V) : V → ℝ := upperShift (wOf k) (-(wOf k)) 0
  have hdOf_mem : ∀ k ∈ Bad, dOf k ∈ S := by
    intro k hk
    have hw : wOf k ∈ S := orthComp_sub (hrOf_mem k hk) (orthComp_smul (rOf k i) hq₁)
    exact (hShift (wOf k) hw (-(wOf k)) (orthComp_neg hw) 0 le_rfl).1
  have hdOf_eq : ∀ k m : V, dOf k m = |wOf k m| := by
    intro k m; simp [dOf, upperShift, abs_eq_max_neg]
  have hdOf_nonneg : ∀ k m : V, 0 ≤ dOf k m := by
    intro k m; rw [hdOf_eq]; exact abs_nonneg _
  have hdOf_i : ∀ k : V, dOf k i = 0 := by
    intro k
    rw [hdOf_eq]
    simp [wOf, hq₁_i]
  let D : V → ℝ := ∑ k ∈ Bad, dOf k
  have hD_mem : D ∈ S := orthComp_sum Bad dOf hdOf_mem
  have hD_nonneg : ∀ m : V, 0 ≤ D m := by
    intro m
    simp only [D, Finset.sum_apply]
    exact Finset.sum_nonneg (fun k _ => hdOf_nonneg k m)
  have hD_i : D i = 0 := by
    simp [D, Finset.sum_apply, hdOf_i]
  have hD_pos : ∀ k ∈ Bad, q₁ k = 1 → 0 < D k := by
    intro k hk hqk1
    have hdk_pos : 0 < dOf k k := by
      rw [hdOf_eq, abs_pos]
      simp only [wOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hqk1, mul_one, sub_ne_zero]
      exact hrOf_ne k hk
    have hle : dOf k k ≤ D k := by
      simp only [D, Finset.sum_apply]
      exact Finset.single_le_sum (fun m _ => hdOf_nonneg m k) hk
    linarith
  let denom : ℝ := 1 + ∑ m : V, D m
  have hdenom_pos : 0 < denom := by
    have hsum_nn : 0 ≤ ∑ m : V, D m := Finset.sum_nonneg (fun m _ => hD_nonneg m)
    dsimp [denom]; linarith
  let q₂ : V → ℝ := q₁ - (1 / denom) • D
  have hq₂_mem : q₂ ∈ S := orthComp_sub hq₁ (orthComp_smul (1 / denom) hD_mem)
  have hq₂_i : q₂ i = 1 := by
    simp [q₂, hq₁_i, hD_i]
  have hq₂_lt_one : ∀ k ∈ Bad, q₂ k < 1 := by
    intro k hk
    simp only [q₂, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rcases lt_or_eq_of_le (hq₁_le_one k) with hlt | heq
    · have hnn : 0 ≤ (1 / denom) * D k := mul_nonneg (by positivity) (hD_nonneg k)
      linarith
    · rw [heq]
      have hpos : 0 < (1 / denom) * D k := mul_pos (by positivity) (hD_pos k hk heq)
      linarith
  let fMax : V → ℝ := fun k => if k ∈ Bad then max 0 (q₂ k) else 0
  let m : ℝ := Finset.sup' Finset.univ ⟨i, Finset.mem_univ i⟩ fMax
  have hi_not_bad : i ∉ Bad := by
    simp [Bad]
  have hm_nonneg : 0 ≤ m := by
    have hle := Finset.le_sup' fMax (Finset.mem_univ i)
    simpa [fMax, hi_not_bad] using hle
  have hm_lt_one : m < 1 := by
    refine (Finset.sup'_lt_iff ⟨i, Finset.mem_univ i⟩).mpr ?_
    intro k _
    dsimp [fMax]
    split_ifs with hk
    · exact max_lt zero_lt_one (hq₂_lt_one k hk)
    · exact zero_lt_one
  have hq₂_le_m : ∀ k ∈ Bad, q₂ k ≤ m := by
    intro k hk
    have hle := Finset.le_sup' fMax (Finset.mem_univ k)
    simp only [fMax, if_pos hk] at hle
    exact (le_max_right 0 (q₂ k)).trans hle
  let u₀ := upperShift q₂ 0 m
  have hu₀_mem : u₀ ∈ S := (hShift q₂ hq₂_mem 0 (orthComp_zero A) m hm_nonneg).1
  have heq : classVec S i = (1 / (1 - m)) • u₀ := by
    ext k
    simp only [classVec, Pi.smul_apply, smul_eq_mul, u₀, upperShift, Pi.sup_apply,
      Pi.sub_apply, Pi.zero_apply, smul_eq_mul, mul_one]
    by_cases hk : ∀ r ∈ S, r k = r i
    · have hq₂k : q₂ k = 1 := by rw [hk q₂ hq₂_mem, hq₂_i]
      rw [if_pos hk, hq₂k]
      have h1m : 0 < 1 - m := by linarith
      rw [max_eq_left h1m.le, one_div_mul_cancel h1m.ne']
    · have hkBad : k ∈ Bad := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      rw [if_neg hk]
      have hle : q₂ k - m ≤ 0 := sub_nonpos.mpr (hq₂_le_m k hkBad)
      rw [max_eq_right hle, mul_zero]
  rw [heq]
  exact orthComp_smul (1 / (1 - m)) hu₀_mem

/-! ### Step C: Forward Direction (`TranslationSubmodularWT (GenQF L K) → CondCPlusGen M Hs`) -/

lemma condCPlusGen_of_translationSubmodularWT (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ))
    (hLsymm : L.IsSymm) (hMsymm : M.IsSymm) (hLpsd : L.PosSemidef) (hMpsd : M.PosSemidef)
    (hK : K = OrthComp (Hs ∩ KerMat M)) (hH : Hs = OrthComp (K ∩ KerMat L))
    (hconj : (∀ p : V → ℝ, ConjugateWT (GenQF M Hs) p = ToEReal2 (GenQF L K p)) ∧
      (∀ x : V → ℝ, ConjugateWT (GenQF L K) x = ToEReal2 (GenQF M Hs x)))
    (hSub : TranslationSubmodularWT (GenQF L K)) :
    CondCPlusGen M Hs := by
  classical
  obtain ⟨hShiftK, hIneqK⟩ := shiftClosed_of_translationSubmodularWT L K hSub
  have hShiftK0 : ShiftClosed (K ∩ KerMat L) :=
    shiftClosed_ker_inter L K hLsymm hLpsd hSub
  have hK0_eq : K ∩ KerMat L = OrthComp Hs := by
    ext q
    exact orthComp_orthComp_ker_iff M L Hs K hMsymm hLsymm hLpsd hH hK q
  have hShiftK0' : ShiftClosed (OrthComp Hs) := hK0_eq ▸ hShiftK0
  have hShiftK' : ShiftClosed (OrthComp (Hs ∩ KerMat M)) := hK ▸ hShiftK
  have h0K : (0 : V → ℝ) ∈ K := by rw [hK]; exact orthComp_zero _
  intro z hz i hi
  have hzi : 0 < z i := by simpa [SuppPosR] using hi
  by_contra hNot
  push_neg at hNot
  obtain ⟨hFail1, hFail2⟩ := hNot
  let p₀ := M.mulVec z
  have hp₀K : p₀ ∈ K := by rw [hK]; exact mulVec_mem_orthComp_ker M hMsymm Hs z
  have hz_sub : z - L.mulVec p₀ ∈ Hs ∩ KerMat M :=
    sub_mulVec_M_mulVec_L_mem M L Hs K hMsymm hLsymm hMpsd hLpsd hH hK ⟨hconj.2, hconj.1⟩ hz
  have hdot_z : ∀ u ∈ K, dotProduct u z = bilin L u p₀ := by
    intro u hu
    have h0 : dotProduct u (z - L.mulVec p₀) = 0 := by
      rw [hK] at hu; exact hu _ hz_sub
    rw [dotProduct_sub] at h0
    unfold bilin
    linarith
  -- Construct p₁ ∈ K with p₁ - p₀ ∈ K ∩ KerMat L, p₁ i ≤ 0, and p₁ j < p₁ i → CharVec i - CharVec j ∈ Hs
  let B : ℝ := |p₀ i| + (∑ k : V, |p₀ k|) + 1
  have hB_pos : 0 < B := by
    have hnn : 0 ≤ ∑ k : V, |p₀ k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
    have hnn0 : 0 ≤ |p₀ i| := abs_nonneg _
    dsimp [B]; linarith
  have hex_p₁ : ∃ p₁ : V → ℝ, p₁ ∈ K ∧ p₁ - p₀ ∈ K ∩ KerMat L ∧ p₁ i ≤ 0 ∧
      ∀ j : V, p₁ j < p₁ i → CharVec i - CharVec j ∈ Hs := by
    by_cases hciH : CharVec i ∈ Hs
    · have hp₀i_le : p₀ i ≤ 0 := (hFail2 hciH).2
      let Bad0 : Finset V := Finset.univ.filter (fun k => CharVec i - CharVec k ∉ Hs)
      have hBad0_ex : ∀ k ∈ Bad0, ∃ r ∈ OrthComp Hs, r k ≠ 0 := by
        intro k hk
        have hk' : CharVec i - CharVec k ∉ Hs := (Finset.mem_filter.mp hk).2
        have hciH' : CharVec i ∈ Hs := hciH
        rw [hH, hK0_eq] at hk' hciH'
        change ¬ (∀ r ∈ OrthComp Hs, dotProduct (CharVec i - CharVec k) r = 0) at hk'
        push_neg at hk'
        obtain ⟨r, hr, hne⟩ := hk'
        have hri : r i = 0 := by
          have h0 := hciH' r hr
          simpa [dot_charVec_left] using h0
        rw [sub_dotProduct, dot_charVec_left, dot_charVec_left, hri, zero_sub, neg_ne_zero] at hne
        exact ⟨r, hr, hne⟩
      let r0Of (k : V) : V → ℝ :=
        if hk : k ∈ Bad0 then Classical.choose (hBad0_ex k hk) else 0
      have hr0_mem : ∀ k ∈ Bad0, r0Of k ∈ OrthComp Hs := by
        intro k hk; simp only [r0Of, dif_pos hk]; exact (Classical.choose_spec (hBad0_ex k hk)).1
      have hr0_ne : ∀ k ∈ Bad0, r0Of k k ≠ 0 := by
        intro k hk; simp only [r0Of, dif_pos hk]; exact (Classical.choose_spec (hBad0_ex k hk)).2
      let d0Of (k : V) : V → ℝ :=
        (1 / |r0Of k k|) • upperShift (r0Of k) (-(r0Of k)) 0
      have hd0_mem : ∀ k ∈ Bad0, d0Of k ∈ OrthComp Hs := by
        intro k hk
        have hr := hr0_mem k hk
        exact orthComp_smul _ ((hShiftK0' (r0Of k) hr (-(r0Of k)) (orthComp_neg hr) 0 le_rfl).1)
      have hd0_eq : ∀ k m : V, d0Of k m = |r0Of k m| / |r0Of k k| := by
        intro k m
        simp [d0Of, upperShift, abs_eq_max_neg, div_eq_inv_mul]
      have hd0_nonneg : ∀ k m : V, 0 ≤ d0Of k m := by
        intro k m; rw [hd0_eq]; positivity
      have hd0_i : ∀ k ∈ Bad0, d0Of k i = 0 := by
        intro k hk
        have hri : r0Of k i = 0 := by
          have hr := hr0_mem k hk
          have hciH' : CharVec i ∈ Hs := hciH
          rw [hH, hK0_eq] at hciH'
          simpa [dot_charVec_left] using hciH' (r0Of k) hr
        rw [hd0_eq, hri, abs_zero, zero_div]
      let D0 : V → ℝ := ∑ k ∈ Bad0, d0Of k
      have hD0_mem : D0 ∈ K ∩ KerMat L := by
        rw [hK0_eq]; exact orthComp_sum Bad0 d0Of hd0_mem
      have hD0_i : D0 i = 0 := by
        simp only [D0, Finset.sum_apply]
        exact Finset.sum_eq_zero hd0_i
      let p₁ := p₀ + B • D0
      have hp₁_sub : p₁ - p₀ ∈ K ∩ KerMat L := by
        have heq : p₁ - p₀ = B • D0 := by ext m; simp [p₁]
        rw [heq, hK0_eq]
        rw [hK0_eq] at hD0_mem
        exact orthComp_smul B hD0_mem
      have hp₁K : p₁ ∈ K := by
        have heq : p₁ = p₀ + (p₁ - p₀) := by ext m; simp
        rw [heq, hK]
        rw [hK] at hp₀K
        have hsubK : p₁ - p₀ ∈ OrthComp (Hs ∩ KerMat M) := hK ▸ hp₁_sub.1
        exact orthComp_add hp₀K hsubK
      have hp₁i : p₁ i ≤ 0 := by
        simp [p₁, hD0_i, hp₀i_le]
      refine ⟨p₁, hp₁K, hp₁_sub, hp₁i, ?_⟩
      intro j hjlt
      by_contra hjNot
      have hjBad : j ∈ Bad0 := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjNot⟩
      have hdj1 : d0Of j j = 1 := by
        rw [hd0_eq, div_self (abs_ne_zero.mpr (hr0_ne j hjBad))]
      have hD0j : 1 ≤ D0 j := by
        rw [← hdj1]
        simp only [D0, Finset.sum_apply]
        exact Finset.single_le_sum (fun k _ => hd0_nonneg k j) hjBad
      have hp₀j_abs : |p₀ j| ≤ ∑ k : V, |p₀ k| :=
        Finset.single_le_sum (fun k _ => abs_nonneg (p₀ k)) (Finset.mem_univ j)
      have hp₀j_lb : -(∑ k : V, |p₀ k|) ≤ p₀ j := by linarith [neg_abs_le (p₀ j)]
      have hp₀i_ub : p₀ i ≤ |p₀ i| := le_abs_self (p₀ i)
      have hBD0 : B ≤ B * D0 j := le_mul_of_one_le_right hB_pos.le hD0j
      have hp₁j_ge : p₁ i ≤ p₁ j := by
        simp only [p₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hD0_i, mul_zero, add_zero]
        dsimp [B] at hBD0 ⊢
        linarith
      exact (not_lt_of_ge hp₁j_ge) hjlt
    · have hex_r₀ : ∃ r₀ ∈ OrthComp Hs, r₀ i ≠ 0 := by
        rw [hH, hK0_eq] at hciH
        change ¬ (∀ r ∈ OrthComp Hs, dotProduct (CharVec i) r = 0) at hciH
        push_neg at hciH
        obtain ⟨r₀, hr₀, hne⟩ := hciH
        rw [dot_charVec_left] at hne
        exact ⟨r₀, hr₀, hne⟩
      let e₀ := classVec (OrthComp Hs) i
      have he₀_mem : e₀ ∈ K ∩ KerMat L := by
        rw [hK0_eq]
        exact classVec_mem_of_shiftClosed Hs hShiftK0' i hex_r₀
      let p₁ := p₀ - B • e₀
      have hp₁_sub : p₁ - p₀ ∈ K ∩ KerMat L := by
        have heq : p₁ - p₀ = (-B) • e₀ := by ext m; simp [p₁]
        rw [heq, hK0_eq]
        rw [hK0_eq] at he₀_mem
        exact orthComp_smul (-B) he₀_mem
      have hp₁K : p₁ ∈ K := by
        have heq : p₁ = p₀ + (p₁ - p₀) := by ext m; simp
        rw [heq, hK]
        rw [hK] at hp₀K
        have hsubK : p₁ - p₀ ∈ OrthComp (Hs ∩ KerMat M) := hK ▸ hp₁_sub.1
        exact orthComp_add hp₀K hsubK
      have hp₁i : p₁ i ≤ 0 := by
        simp only [p₁, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e₀, classVec_self, mul_one]
        have hp₀i_ub : p₀ i ≤ |p₀ i| := le_abs_self (p₀ i)
        have hnn : 0 ≤ ∑ k : V, |p₀ k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
        dsimp [B]
        linarith
      refine ⟨p₁, hp₁K, hp₁_sub, hp₁i, ?_⟩
      intro j hjlt
      by_contra hjNot
      have hnot_eq : ¬ ∀ r ∈ OrthComp Hs, r j = r i := by
        intro hall
        apply hjNot
        rw [hH, hK0_eq]
        intro r hr
        rw [sub_dotProduct, dot_charVec_left, dot_charVec_left, hall r hr, sub_self]
      have he₀j : e₀ j = 0 := by simp [e₀, classVec, hnot_eq]
      have hp₀j_abs : |p₀ j| ≤ ∑ k : V, |p₀ k| :=
        Finset.single_le_sum (fun k _ => abs_nonneg (p₀ k)) (Finset.mem_univ j)
      have hp₀j_lb : -(∑ k : V, |p₀ k|) ≤ p₀ j := by linarith [neg_abs_le (p₀ j)]
      have hp₀i_ub : p₀ i ≤ |p₀ i| := le_abs_self (p₀ i)
      have hp₁j_ge : p₁ i ≤ p₁ j := by
        simp only [p₁, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e₀, classVec_self, he₀j,
          mul_one, mul_zero, sub_zero]
        dsimp [B]
        linarith
      exact (not_lt_of_ge hp₁j_ge) hjlt
  obtain ⟨p₁, hp₁K, hp₁_sub, hp₁i, hp₁_lt_imp⟩ := hex_p₁
  have hLp₁ : L.mulVec p₁ = L.mulVec p₀ := by
    have hker : L.mulVec (p₁ - p₀) = 0 := hp₁_sub.2
    rw [Matrix.mulVec_sub, sub_eq_zero] at hker
    exact hker
  have hp₁_diff_eq : ∀ j : V, CharVec i - CharVec j ∈ Hs → p₁ i - p₁ j = p₀ i - p₀ j := by
    intro j hijH
    have h0 : dotProduct (p₁ - p₀) (CharVec i - CharVec j) = 0 := by
      have hmem : p₁ - p₀ ∈ OrthComp Hs := hK0_eq ▸ hp₁_sub
      exact hmem _ hijH
    rw [dotProduct_sub, sub_dotProduct, sub_dotProduct,
      dot_charVec_right, dot_charVec_right, dot_charVec_right, dot_charVec_right] at h0
    linarith
  have hz_nonneg_of_lt : ∀ j : V, p₁ j < p₁ i → 0 ≤ z j := by
    intro j hjlt
    have hijH : CharVec i - CharVec j ∈ Hs := hp₁_lt_imp j hjlt
    have hdiff := hp₁_diff_eq j hijH
    have hp₀_lt : p₀ j < p₀ i := by linarith
    by_contra hzj
    have hzj' : j ∈ SuppNegR z := by
      have hlt : z j < 0 := by linarith
      simpa [SuppNegR] using hlt
    have hle := (hFail1 j hzj' hijH).2
    exact (not_lt_of_ge hle) hp₀_lt
  -- Truncate p₁ at floor p₁ i ≤ 0
  have ha_nn : 0 ≤ -p₁ i := neg_nonneg.mpr hp₁i
  let u := upperShift 0 p₁ (-p₁ i)
  let v := lowerShift 0 p₁ (-p₁ i)
  obtain ⟨huK, hvK⟩ := hShiftK 0 h0K p₁ hp₁K (-p₁ i) ha_nn
  have huv_ineq := hIneqK 0 h0K p₁ hp₁K (-p₁ i) ha_nn
  have huv_add : u + v = p₁ := by
    ext k
    simp only [u, v, upperShift, lowerShift, Pi.add_apply, Pi.sup_apply, Pi.inf_apply,
      Pi.sub_apply, Pi.neg_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, mul_one,
      zero_sub, neg_neg]
    rcases le_total (p₁ i) (p₁ k) with hle | hle
    · have hle' : 0 ≤ p₁ k + -p₁ i := by linarith
      rw [max_eq_right hle, min_eq_left hle', add_zero]
    · have hle' : p₁ k + -p₁ i ≤ 0 := by linarith
      rw [max_eq_left hle, min_eq_right hle']
      ring
  have hbil_vu_nonneg : 0 ≤ bilin L v u := by
    have hqp₁ : QF L p₁ = QF L u + QF L v + bilin L v u := by
      rw [← huv_add, qf_add L hLsymm u v, bilin_symm L hLsymm u v]
    have hqf0 : QF L (0 : V → ℝ) = 0 := qf_zero L
    linarith
  have hv_dot_z_nonpos : dotProduct v z ≤ 0 := by
    apply Finset.sum_nonpos
    intro k _
    by_cases hlt : p₁ k < p₁ i
    · have hvk : v k ≤ 0 := by
        simp only [v, lowerShift, Pi.inf_apply, Pi.zero_apply, min_le_iff]
        exact Or.inl le_rfl
      exact mul_nonpos_of_nonpos_of_nonneg hvk (hz_nonneg_of_lt k hlt)
    · have hge : 0 ≤ p₁ k + -p₁ i := by linarith
      have hvk : v k = 0 := by
        simp only [v, lowerShift, Pi.inf_apply, Pi.zero_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, mul_one, min_eq_left hge]
      rw [hvk, zero_mul]
  have hv_dot_z_eq : dotProduct v z = 2 * QF L v + bilin L v u := by
    rw [hdot_z v hvK, bilin, ← hLp₁, ← huv_add, Matrix.mulVec_add, dotProduct_add,
      ← bilin_self_eq_two_qf L v]
    unfold bilin
    ring
  have hqfv_nn := qf_nonneg L hLpsd v
  have hqfv_zero : QF L v = 0 := by linarith
  have hLv : L.mulVec v = 0 := (qf_eq_zero_iff L hLsymm hLpsd v).mp hqfv_zero
  have hLu : L.mulVec u = L.mulVec p₀ := by
    rw [← hLp₁, ← huv_add, Matrix.mulVec_add, hLv, add_zero]
  have hui : u i = p₁ i := by
    simp [u, upperShift]
  have hui_le : u i ≤ 0 := hui ▸ hp₁i
  have hu_ge : ∀ k : V, u i ≤ u k := by
    intro k
    simp [u, upperShift, hui]
  -- Test u against e_i = classVec K i
  have hex_qK : ∃ q ∈ OrthComp (Hs ∩ KerMat M), q i ≠ 0 := by
    by_contra hAll0
    push_neg at hAll0
    have hci_mem : CharVec i ∈ Hs ∩ KerMat M := by
      rw [orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH]
      intro q hq
      rw [dot_charVec_left]
      exact hAll0 q (hK ▸ hq)
    exact (hFail2 hci_mem.1).1 hci_mem.2
  let e_i := classVec (OrthComp (Hs ∩ KerMat M)) i
  have he_iK : e_i ∈ K := by
    rw [hK]
    exact classVec_mem_of_shiftClosed (Hs ∩ KerMat M) hShiftK' i hex_qK
  let u' := u - e_i
  have hu'K : u' ∈ K := by
    rw [hK] at huK he_iK ⊢
    exact orthComp_sub huK he_iK
  have ha_u_nn : 0 ≤ -u i := neg_nonneg.mpr hui_le
  have hupper_u' : upperShift 0 u' (-u i) = u := by
    ext k
    simp only [upperShift, u', e_i, classVec, Pi.sup_apply, Pi.sub_apply, Pi.neg_apply,
      Pi.zero_apply, Pi.smul_apply, smul_eq_mul, mul_one, zero_sub, neg_neg]
    split_ifs with hk
    · have huk : u k = u i := hk u (hK ▸ huK)
      rw [huk]
      exact max_eq_left (by linarith)
    · rw [sub_zero]
      exact max_eq_right (hu_ge k)
  have hlower_u' : lowerShift 0 u' (-u i) = -e_i := by
    ext k
    simp only [lowerShift, u', e_i, classVec, Pi.inf_apply, Pi.add_apply,
      Pi.sub_apply, Pi.neg_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    split_ifs with hk
    · have huk : u k = u i := hk u (hK ▸ huK)
      rw [huk]
      have h1 : u i - 1 + -u i = -1 := by ring
      rw [h1]
      exact min_eq_right (by norm_num)
    · have hge : 0 ≤ u k - 0 + -u i := by linarith [hu_ge k]
      rw [min_eq_left hge, neg_zero]
  have hineq_u' := hIneqK 0 h0K u' hu'K (-u i) ha_u_nn
  rw [hupper_u', hlower_u', qf_zero, zero_add, qf_neg, qf_sub L hLsymm u e_i,
    bilin_symm L hLsymm u e_i] at hineq_u'
  have hbil_ei_u : bilin L e_i u ≤ 0 := by linarith
  have hdot_ei_z : dotProduct e_i z ≤ 0 := by
    rw [hdot_z e_i he_iK, bilin, ← hLu]
    exact hbil_ei_u
  let C_i : Finset V := Finset.univ.filter (fun k => ∀ r ∈ OrthComp (Hs ∩ KerMat M), r k = r i)
  have hsum_Ci : ∑ k ∈ C_i, z k = dotProduct e_i z := by
    simp only [dotProduct, e_i, classVec, C_i, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  have hi_mem_Ci : i ∈ C_i := by simp [C_i]
  have hex_neg : ∃ j ∈ C_i, z j < 0 := by
    by_contra hAll_nn
    push_neg at hAll_nn
    have hpos_sum : 0 < ∑ k ∈ C_i, z k :=
      Finset.sum_pos' (fun k hk => hAll_nn k hk) ⟨i, hi_mem_Ci, hzi⟩
    linarith
  obtain ⟨j, hjCi, hzj_neg⟩ := hex_neg
  have hj_suppNeg : j ∈ SuppNegR z := by simpa [SuppNegR] using hzj_neg
  have hij_mem : CharVec i - CharVec j ∈ Hs ∩ KerMat M := by
    rw [orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH]
    intro q hq
    have hqj := (Finset.mem_filter.mp hjCi).2 q (hK ▸ hq)
    rw [sub_dotProduct, dot_charVec_left, dot_charVec_left, hqj, sub_self]
  exact (hFail1 j hj_suppNeg hij_mem.1).1 hij_mem.2

/-! ### Step D: Backward Direction (`CondCPlusGen M Hs → TranslationSubmodularWT (GenQF L K)`) -/

noncomputable def rowSum (L : Matrix V V ℝ) (i : V) : ℝ :=
  ∑ j, L i j

lemma row_square_sum (L : Matrix V V ℝ) (p : V → ℝ) :
    (∑ i, ∑ j, L i j * (p i) ^ 2) = ∑ i, rowSum L i * (p i) ^ 2 := by
  simp only [rowSum, Finset.sum_mul]

lemma column_square_sum (L : Matrix V V ℝ) (hL : L.IsSymm) (p : V → ℝ) :
    (∑ i, ∑ j, L i j * (p j) ^ 2) = ∑ i, rowSum L i * (p i) ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [hL.apply i]
  simp only [rowSum, Finset.sum_mul]

lemma edge_energy_identity (L : Matrix V V ℝ) (hL : L.IsSymm) (p : V → ℝ) :
    (∑ i, ∑ j, L i j * (p i - p j) ^ 2) =
      2 * (∑ i, rowSum L i * (p i) ^ 2) - 2 * bilin L p p := by
  calc
    (∑ i, ∑ j, L i j * (p i - p j) ^ 2) =
        (∑ i, ∑ j, L i j * (p i) ^ 2) + (∑ i, ∑ j, L i j * (p j) ^ 2) -
          2 * (∑ i, ∑ j, L i j * (p i * p j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 2 * (∑ i, rowSum L i * (p i) ^ 2) - 2 * bilin L p p := by
      rw [row_square_sum, column_square_sum L hL, ← bilin_eq_sum]
      ring

lemma energy_decomposition (L : Matrix V V ℝ) (hL : L.IsSymm) (p : V → ℝ) :
    QF L p = (1 / 2 : ℝ) * (∑ i, rowSum L i * (p i) ^ 2) -
      (1 / 4 : ℝ) * (∑ i, ∑ j, L i j * (p i - p j) ^ 2) := by
  have h := edge_energy_identity L hL p
  change (1 / 2 : ℝ) * bilin L p p = _
  linarith

noncomputable def reflection (a t : ℝ) : ℝ := |t - a| - a

lemma reflection_lipschitz (a s t : ℝ) :
    |reflection a s - reflection a t| ≤ |s - t| := by
  have h := abs_abs_sub_abs_le_abs_sub (s - a) (t - a)
  have hleft : reflection a s - reflection a t = |s - a| - |t - a| := by
    unfold reflection; ring
  have hright : (s - a) - (t - a) = s - t := by ring
  rw [hleft]
  simpa only [hright] using h

lemma reflection_zero (a : ℝ) (ha : 0 ≤ a) : reflection a 0 = 0 := by
  simp [reflection, abs_of_nonneg ha]

lemma reflection_square (a s : ℝ) (ha : 0 ≤ a) : (reflection a s) ^ 2 ≤ s ^ 2 := by
  apply sq_le_sq.mpr
  have h := reflection_lipschitz a s 0
  simpa only [reflection_zero a ha, sub_zero] using h

lemma reflection_edge_square (a s t : ℝ) :
    (reflection a s - reflection a t) ^ 2 ≤ (s - t) ^ 2 :=
  sq_le_sq.mpr (reflection_lipschitz a s t)

lemma shifted_max_min (p q a : ℝ) :
    max (p - a) q + min p (q + a) = p + q ∧
    max (p - a) q - min p (q + a) = reflection a (p - q) := by
  by_cases h : p - q ≤ a
  · have h1 : p - a ≤ q := by linarith
    have h2 : p ≤ q + a := by linarith
    rw [max_eq_right h1, min_eq_left h2]
    refine ⟨by ring, ?_⟩
    unfold reflection
    rw [abs_of_nonpos (by linarith : p - q - a ≤ 0)]
    ring
  · have h1 : q ≤ p - a := by linarith
    have h2 : q + a ≤ p := by linarith
    rw [max_eq_left h1, min_eq_right h2]
    refine ⟨by ring, ?_⟩
    unfold reflection
    rw [abs_of_nonneg (by linarith : 0 ≤ p - q - a)]
    ring

lemma shifted_pair_shape (p q : V → ℝ) (a : ℝ) :
    upperShift p q a + lowerShift p q a = p + q ∧
    ∀ i, (upperShift p q a - lowerShift p q a) i = reflection a ((p - q) i) := by
  constructor
  · ext i
    simpa [upperShift, lowerShift, Pi.sup_apply, Pi.inf_apply, smul_eq_mul] using
      (shifted_max_min (p i) (q i) a).1
  · intro i
    simpa [upperShift, lowerShift, Pi.sup_apply, Pi.inf_apply, smul_eq_mul] using
      (shifted_max_min (p i) (q i) a).2

lemma bilin_sum_left (L : Matrix V V ℝ) {ι : Type*} (s : Finset ι) (f : ι → V → ℝ) (q : V → ℝ) :
    bilin L (∑ i ∈ s, f i) q = ∑ i ∈ s, bilin L (f i) q := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp [bilin]
  · rw [Finset.sum_insert ha, bilin_add_left, ih, Finset.sum_insert ha]

lemma bilin_sum_right (L : Matrix V V ℝ) {ι : Type*} (p : V → ℝ) (s : Finset ι) (f : ι → V → ℝ) :
    bilin L p (∑ i ∈ s, f i) = ∑ i ∈ s, bilin L p (f i) := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp [bilin]
  · rw [Finset.sum_insert ha, bilin_add_right, ih, Finset.sum_insert ha]

lemma exists_lt_of_bilin_pos (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ))
    (hLsymm : L.IsSymm) (hMsymm : M.IsSymm) (hLpsd : L.PosSemidef) (hMpsd : M.PosSemidef)
    (hK : K = OrthComp (Hs ∩ KerMat M)) (hH : Hs = OrthComp (K ∩ KerMat L))
    (hconj : (∀ p : V → ℝ, ConjugateWT (GenQF M Hs) p = ToEReal2 (GenQF L K p)) ∧
      (∀ x : V → ℝ, ConjugateWT (GenQF L K) x = ToEReal2 (GenQF M Hs x)))
    (hC : CondCPlusGen M Hs)
    {p : V → ℝ} (hp : p ∈ K) {i : V} (hi : CharVec i ∉ Hs ∩ KerMat M)
    (hpos : 0 < bilin L (fun k => if CharVec i - CharVec k ∈ Hs ∩ KerMat M then (1 : ℝ) else 0) p) :
    0 < p i ∨ ∃ k : V, CharVec i - CharVec k ∉ Hs ∩ KerMat M ∧ p k < p i := by
  classical
  let S₀ := Hs ∩ KerMat M
  have hS₀_eq : S₀ = OrthComp K := by
    ext z
    exact orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH z
  let C_i : Finset V := Finset.univ.filter (fun k => CharVec i - CharVec k ∈ S₀)
  have hi_Ci : i ∈ C_i := by
    simp only [C_i, Finset.mem_filter, Finset.mem_univ, true_and, sub_self]
    rw [hS₀_eq]; exact orthComp_zero K
  have hCi_pos : (0 : ℝ) < (C_i.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨i, hi_Ci⟩
  let z₀ := L.mulVec p
  have hz₀_Hs : z₀ ∈ Hs := by rw [hH]; exact mulVec_mem_orthComp_ker L hLsymm K p
  have hsum_z₀ : ∑ r ∈ C_i, z₀ r =
      bilin L (fun k => if CharVec i - CharVec k ∈ S₀ then (1 : ℝ) else 0) p := by
    simp only [bilin, dotProduct, C_i, Finset.sum_filter, z₀]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  let avg : ℝ := (∑ r ∈ C_i, z₀ r) / (C_i.card : ℝ)
  have havg_pos : 0 < avg := div_pos (hsum_z₀.symm ▸ hpos) hCi_pos
  let diffSum : V → ℝ := ∑ m ∈ C_i, (z₀ m - avg) • (CharVec m - CharVec i)
  have hdiff_S₀ : diffSum ∈ S₀ := by
    rw [hS₀_eq]
    refine orthComp_sum C_i _ (fun m hm => ?_)
    have hm' : CharVec i - CharVec m ∈ OrthComp K := hS₀_eq ▸ (Finset.mem_filter.mp hm).2
    have hmi : CharVec m - CharVec i = -(CharVec i - CharVec m) := by ext k; simp
    rw [hmi]
    exact orthComp_smul (z₀ m - avg) (orthComp_neg hm')
  let z : V → ℝ := z₀ - diffSum
  have hz_Hs : z ∈ Hs := by
    rw [hH] at hz₀_Hs ⊢
    have hdiff_Hs : diffSum ∈ OrthComp (K ∩ KerMat L) := hH ▸ hdiff_S₀.1
    exact orthComp_sub hz₀_Hs hdiff_Hs
  have hMz_eq : M.mulVec z = M.mulVec z₀ := by
    simp only [z, Matrix.mulVec_sub]
    have hker : M.mulVec diffSum = 0 := hdiff_S₀.2
    rw [hker, sub_zero]
  have hsum_coeff_zero : ∑ m ∈ C_i, (z₀ m - avg) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    dsimp [avg]
    rw [mul_div_cancel₀ _ hCi_pos.ne', sub_self]
  have hz_eval : ∀ k : V, z k = if k ∈ C_i then avg else z₀ k := by
    intro k
    have hds : diffSum k = (if k ∈ C_i then z₀ k - avg else 0) -
        (∑ m ∈ C_i, (z₀ m - avg)) * CharVec i k := by
      simp only [diffSum, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      congr 1
      simp only [CharVec, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
    rw [hsum_coeff_zero, zero_mul, sub_zero] at hds
    simp only [z, Pi.sub_apply, hds]
    split_ifs <;> ring
  have hzi : i ∈ SuppPosR z := by
    have hgt : 0 < z i := by rw [hz_eval i, if_pos hi_Ci]; exact havg_pos
    simpa [SuppPosR] using hgt
  rcases hC z hz_Hs i hzi with ⟨k, hk_neg, hik_Hs, hker | hlt⟩ | ⟨hi_Hs, hker | hlt⟩
  · have hzk_lt : z k < 0 := by simpa [SuppNegR] using hk_neg
    have hk_not_Ci : k ∉ C_i := by
      intro hkCi
      rw [hz_eval k, if_pos hkCi] at hzk_lt
      linarith
    have hik_not_S₀ : CharVec i - CharVec k ∉ S₀ := by
      intro hmem
      exact hk_not_Ci (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hmem⟩)
    exact absurd ⟨hik_Hs, hker⟩ hik_not_S₀
  · have hzk_lt : z k < 0 := by simpa [SuppNegR] using hk_neg
    have hk_not_Ci : k ∉ C_i := by
      intro hkCi
      rw [hz_eval k, if_pos hkCi] at hzk_lt
      linarith
    have hik_not_S₀ : CharVec i - CharVec k ∉ S₀ := by
      intro hmem
      exact hk_not_Ci (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hmem⟩)
    right
    refine ⟨k, hik_not_S₀, ?_⟩
    have hdot := dotProduct_mulVec_M_mulVec_L_eq L M K Hs hLsymm hMsymm hLpsd hMpsd
      hK hH hconj hp hik_Hs
    rw [sub_dotProduct, dot_charVec_left, dot_charVec_left,
      sub_dotProduct, dot_charVec_left, dot_charVec_left] at hdot
    rw [hMz_eq] at hlt
    linarith
  · exact absurd ⟨hi_Hs, hker⟩ hi
  · left
    have hdot := dotProduct_mulVec_M_mulVec_L_eq L M K Hs hLsymm hMsymm hLpsd hMpsd
      hK hH hconj hp hi_Hs
    rw [dot_charVec_left, dot_charVec_left] at hdot
    rw [hMz_eq] at hlt
    linarith

lemma translationSubmodularWT_of_condCPlusGen (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ))
    (hLsymm : L.IsSymm) (hMsymm : M.IsSymm) (hLpsd : L.PosSemidef) (hMpsd : M.PosSemidef)
    (hK : K = OrthComp (Hs ∩ KerMat M)) (hH : Hs = OrthComp (K ∩ KerMat L))
    (hconj : (∀ p : V → ℝ, ConjugateWT (GenQF M Hs) p = ToEReal2 (GenQF L K p)) ∧
      (∀ x : V → ℝ, ConjugateWT (GenQF L K) x = ToEReal2 (GenQF M Hs x)))
    (hC : CondCPlusGen M Hs) :
    TranslationSubmodularWT (GenQF L K) := by
  classical
  let S₀ := Hs ∩ KerMat M
  have hB : ∀ z ∈ OrthComp K, ∀ i ∈ SuppPosR z,
      CharVec i ∈ OrthComp K ∨ ∃ j ∈ SuppNegR z, CharVec i - CharVec j ∈ OrthComp K := by
    intro z hz i hi
    have hzS₀ : z ∈ S₀ :=
      (orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH z).mpr hz
    have hMz : M.mulVec z = 0 := hzS₀.2
    rcases hC z hzS₀.1 i hi with ⟨j, hj, hijH, hker | hlt⟩ | ⟨hiH, hker | hlt⟩
    · right
      refine ⟨j, hj, ?_⟩
      exact (orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH _).mp ⟨hijH, hker⟩
    · rw [hMz] at hlt; simp at hlt
    · left
      exact (orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH _).mp ⟨hiH, hker⟩
    · rw [hMz] at hlt; simp at hlt
  have hK_mem_iff : ∀ u : V → ℝ,
      (∀ i : V, CharVec i ∈ S₀ → u i = 0) →
      (∀ i j : V, CharVec i - CharVec j ∈ S₀ → u i = u j) →
      u ∈ K := by
    intro u h1 h2
    have h1' : ∀ i : V, CharVec i ∈ OrthComp K → u i = 0 := by
      intro i hi
      exact h1 i ((orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH _).mpr hi)
    have h2' : ∀ i j : V, CharVec i - CharVec j ∈ OrthComp K → u i = u j := by
      intro i j hij
      exact h2 i j ((orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH _).mpr hij)
    have hu := orth_of_charVec_orth K hB u h1' h2'
    rw [hK]
    intro z hz
    exact hu z ((orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH z).mp hz)
  have hK_zero : ∀ p ∈ K, ∀ i : V, CharVec i ∈ S₀ → p i = 0 := by
    intro p hp i hi
    rw [hK] at hp
    simpa [dot_charVec_right] using hp (CharVec i) hi
  have hK_eq_of_rel : ∀ p ∈ K, ∀ i j : V, CharVec i - CharVec j ∈ S₀ → p i = p j := by
    intro p hp i j hij
    rw [hK] at hp
    have h0 := hp (CharVec i - CharVec j) hij
    rw [dotProduct_sub, dot_charVec_right, dot_charVec_right, sub_eq_zero] at h0
    exact h0
  have hS₀_refl : ∀ i : V, CharVec i - CharVec i ∈ S₀ := by
    intro i; rw [sub_self, orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH]
    exact orthComp_zero K
  have hS₀_symm : ∀ i j : V, CharVec i - CharVec j ∈ S₀ → CharVec j - CharVec i ∈ S₀ := by
    intro i j hij
    rw [orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH] at hij ⊢
    have hneg : CharVec j - CharVec i = -(CharVec i - CharVec j) := by ext k; simp
    rw [hneg]; exact orthComp_neg hij
  have hS₀_trans : ∀ i j k : V,
      CharVec i - CharVec j ∈ S₀ → CharVec j - CharVec k ∈ S₀ → CharVec i - CharVec k ∈ S₀ := by
    intro i j k hij hjk
    rw [orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH] at hij hjk ⊢
    have hadd : CharVec i - CharVec k = (CharVec i - CharVec j) + (CharVec j - CharVec k) := by
      ext m; simp
    rw [hadd]; exact orthComp_add hij hjk
  have hS₀_single : ∀ i j : V,
      CharVec i ∈ S₀ → CharVec i - CharVec j ∈ S₀ → CharVec j ∈ S₀ := by
    intro i j hi hij
    rw [orthComp_orthComp_ker_iff L M K Hs hLsymm hMsymm hMpsd hK hH] at hi hij ⊢
    have hsub : CharVec j = CharVec i - (CharVec i - CharVec j) := by ext m; simp
    rw [hsub]; exact orthComp_sub hi hij
  -- Shift-closure of K
  have hShiftK : ShiftClosed K := by
    intro p hp q hq a ha
    constructor
    · apply hK_mem_iff
      · intro i hi
        simp [upperShift, hK_zero p hp i hi, hK_zero q hq i hi, ha]
      · intro i j hij
        simp [upperShift, hK_eq_of_rel p hp i j hij, hK_eq_of_rel q hq i j hij]
    · apply hK_mem_iff
      · intro i hi
        simp [lowerShift, hK_zero p hp i hi, hK_zero q hq i hi, ha]
      · intro i j hij
        simp [lowerShift, hK_eq_of_rel p hp i j hij, hK_eq_of_rel q hq i j hij]
  -- Equivalence class indicators eVec, wVec, oneK, and matrix Ltilde
  let EqCl (i : V) : Finset V := Finset.univ.filter (fun k => CharVec i - CharVec k ∈ S₀)
  let eVec (i : V) : V → ℝ := fun k => if CharVec i - CharVec k ∈ S₀ then 1 else 0
  let wVec (i : V) : V → ℝ :=
    if CharVec i ∈ S₀ then 0 else ((1 : ℝ) / ((EqCl i).card : ℝ)) • eVec i
  let oneK : V → ℝ := fun k => if CharVec k ∈ S₀ then 0 else 1
  have heVec_mem : ∀ i : V, CharVec i ∉ S₀ → eVec i ∈ K := by
    intro i hi
    apply hK_mem_iff
    · intro k hk
      have hnot : CharVec i - CharVec k ∉ S₀ := fun h =>
        hi (hS₀_single k i hk (hS₀_symm i k h))
      simp [eVec, hnot]
    · intro k m hkm
      by_cases hik : CharVec i - CharVec k ∈ S₀
      · have him : CharVec i - CharVec m ∈ S₀ := hS₀_trans i k m hik hkm
        simp [eVec, hik, him]
      · have him : CharVec i - CharVec m ∉ S₀ := fun h =>
          hik (hS₀_trans i m k h (hS₀_symm k m hkm))
        simp [eVec, hik, him]
  have honeK_mem : oneK ∈ K := by
    apply hK_mem_iff
    · intro i hi; simp [oneK, hi]
    · intro i j hij
      by_cases hi : CharVec i ∈ S₀
      · have hj : CharVec j ∈ S₀ := hS₀_single i j hi hij
        simp [oneK, hi, hj]
      · have hj : CharVec j ∉ S₀ := fun h => hi (hS₀_single j i h (hS₀_symm i j hij))
        simp [oneK, hi, hj]
  have hEqCl_eq : ∀ i k : V, CharVec i - CharVec k ∈ S₀ → EqCl i = EqCl k := by
    intro i k hik
    ext m
    simp only [EqCl, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun him => hS₀_trans k i m (hS₀_symm i k hik) him,
      fun hkm => hS₀_trans i k m hik hkm⟩
  have hEqCl_card_pos : ∀ k : V, (0 : ℝ) < ((EqCl k).card : ℝ) := by
    intro k
    have hk : k ∈ EqCl k := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hS₀_refl k⟩
    exact_mod_cast Finset.card_pos.mpr ⟨k, hk⟩
  have hsum_wVec : ∀ p ∈ K, (∑ i : V, p i • wVec i) = p := by
    intro p hp
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hk : CharVec k ∈ S₀
    · rw [hK_zero p hp k hk]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : CharVec i ∈ S₀
      · simp [wVec, hi]
      · have hik : CharVec i - CharVec k ∉ S₀ := fun h =>
          hi (hS₀_single k i hk (hS₀_symm i k h))
        simp [wVec, hi, eVec, hik]
    · have hterm : ∀ i : V, p i * wVec i k =
          if i ∈ EqCl k then p k * (1 / ((EqCl k).card : ℝ)) else 0 := by
        intro i
        by_cases hki : CharVec k - CharVec i ∈ S₀
        · have hik : CharVec i - CharVec k ∈ S₀ := hS₀_symm k i hki
          have hi : CharVec i ∉ S₀ := fun h => hk (hS₀_single i k h hik)
          have hpi : p i = p k := hK_eq_of_rel p hp i k hik
          have hcl : EqCl i = EqCl k := hEqCl_eq i k hik
          have hi_mem : i ∈ EqCl k := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hki⟩
          simp [wVec, hi, eVec, hik, hpi, hcl, hi_mem]
        · have hik : CharVec i - CharVec k ∉ S₀ := fun h => hki (hS₀_symm i k h)
          have hi_not : i ∉ EqCl k := by simp [EqCl, hki]
          by_cases hi : CharVec i ∈ S₀ <;> simp [wVec, hi, eVec, hik, hi_not]
      simp_rw [hterm]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.sum_const, nsmul_eq_mul]
      have hne : ((EqCl k).card : ℝ) ≠ 0 := (hEqCl_card_pos k).ne'
      field_simp [hne]
  let Ltilde : Matrix V V ℝ := fun i j => bilin L (wVec i) (wVec j)
  have hLtilde_symm : Ltilde.IsSymm := by
    ext i j
    exact bilin_symm L hLsymm (wVec j) (wVec i)
  have hQF_Ltilde : ∀ p ∈ K, QF Ltilde p = QF L p := by
    intro p hp
    change (1 / 2 : ℝ) * bilin Ltilde p p = (1 / 2 : ℝ) * bilin L p p
    congr 1
    rw [bilin_eq_sum Ltilde p p]
    conv_rhs => rw [← hsum_wVec p hp]
    rw [bilin_sum_left, Finset.sum_congr rfl]
    intro i _
    rw [bilin_sum_right, Finset.sum_congr rfl]
    intro j _
    rw [bilin_smul_left, bilin_smul_right]
    dsimp [Ltilde]
    ring
  have hrowSum_Ltilde : ∀ i : V, rowSum Ltilde i = bilin L (wVec i) oneK := by
    intro i
    unfold rowSum
    have hsum_one : (∑ j : V, wVec j) = oneK := by
      have h := hsum_wVec oneK honeK_mem
      have hterm : ∀ j : V, oneK j • wVec j = wVec j := by
        intro j
        by_cases hj : CharVec j ∈ S₀ <;> simp [oneK, wVec, hj]
      simp_rw [hterm] at h
      exact h
    rw [← hsum_one, bilin_sum_right]
  have hOff_Ltilde : ∀ i j : V, CharVec i - CharVec j ∉ S₀ → Ltilde i j ≤ 0 := by
    intro i j hij
    dsimp [Ltilde]
    by_cases hi : CharVec i ∈ S₀
    · have hwi : wVec i = 0 := if_pos hi
      rw [hwi]; unfold bilin; rw [zero_dotProduct]
    · by_cases hj : CharVec j ∈ S₀
      · have hwj : wVec j = 0 := if_pos hj
        rw [hwj]; unfold bilin; rw [Matrix.mulVec_zero, dotProduct_zero]
      · have hwi : wVec i = ((1 : ℝ) / ((EqCl i).card : ℝ)) • eVec i := if_neg hi
        have hwj : wVec j = ((1 : ℝ) / ((EqCl j).card : ℝ)) • eVec j := if_neg hj
        rw [hwi, hwj, bilin_smul_left, bilin_smul_right]
        have hc1 : 0 ≤ (1 : ℝ) / ((EqCl i).card : ℝ) :=
          div_nonneg zero_le_one (hEqCl_card_pos i).le
        have hc2 : 0 ≤ (1 : ℝ) / ((EqCl j).card : ℝ) :=
          div_nonneg zero_le_one (hEqCl_card_pos j).le
        suffices hle : bilin L (eVec i) (eVec j) ≤ 0 by
          exact mul_nonpos_of_nonneg_of_nonpos hc1 (mul_nonpos_of_nonneg_of_nonpos hc2 hle)
        by_contra hgt
        have hpos : 0 < bilin L (eVec i) (eVec j) := lt_of_not_ge hgt
        have hejK : eVec j ∈ K := heVec_mem j hj
        have heji : eVec j i = 0 := by
          have hji : CharVec j - CharVec i ∉ S₀ := fun h => hij (hS₀_symm j i h)
          simp [eVec, hji]
        rcases exists_lt_of_bilin_pos L M K Hs hLsymm hMsymm hLpsd hMpsd
          hK hH hconj hC hejK hi hpos with h1 | ⟨k, _, hlt⟩
        · rw [heji] at h1; exact lt_irrefl 0 h1
        · rw [heji] at hlt
          have hnn : 0 ≤ eVec j k := by unfold eVec; split_ifs <;> norm_num
          exact (not_lt_of_ge hnn) hlt
  have hRow_Ltilde : ∀ i : V, 0 ≤ rowSum Ltilde i := by
    intro i
    rw [hrowSum_Ltilde]
    by_cases hi : CharVec i ∈ S₀
    · have hwi : wVec i = 0 := if_pos hi
      rw [hwi]; unfold bilin; rw [zero_dotProduct]
    · have hwi : wVec i = ((1 : ℝ) / ((EqCl i).card : ℝ)) • eVec i := if_neg hi
      rw [hwi, bilin_smul_left]
      have hc1 : 0 ≤ (1 : ℝ) / ((EqCl i).card : ℝ) :=
        div_nonneg zero_le_one (hEqCl_card_pos i).le
      suffices hge : 0 ≤ bilin L (eVec i) oneK by
        exact mul_nonneg hc1 hge
      by_contra hlt
      have hpos : 0 < bilin L (eVec i) (-oneK) := by
        have hneg : (-oneK : V → ℝ) = (-1 : ℝ) • oneK := by ext k; simp
        rw [hneg, bilin_smul_right]
        linarith
      have hneg_oneK : -oneK ∈ K := by
        rw [hK] at honeK_mem ⊢; exact orthComp_neg honeK_mem
      have h_oneK_i : (-oneK) i = -1 := by simp [oneK, hi]
      rcases exists_lt_of_bilin_pos L M K Hs hLsymm hMsymm hLpsd hMpsd
        hK hH hconj hC hneg_oneK hi hpos with h1 | ⟨k, _, hlt'⟩
      · rw [h_oneK_i] at h1; norm_num at h1
      · rw [h_oneK_i] at hlt'
        have hge' : -1 ≤ (-oneK) k := by
          simp only [Pi.neg_apply, oneK]
          split_ifs <;> norm_num
        exact (not_lt_of_ge hge') hlt'
  -- Assemble TranslationSubmodularWT (GenQF L K)
  intro p q a ha
  by_cases hp : p ∈ K
  · by_cases hq : q ∈ K
    · obtain ⟨huK, hvK⟩ := hShiftK p hp q hq a ha
      change GenQF L K p + GenQF L K q ≥
        GenQF L K (upperShift p q a) + GenQF L K (lowerShift p q a)
      simp only [GenQF, hp, hq, huK, hvK, ↓reduceIte, ge_iff_le,
        ← WithTop.coe_add, WithTop.coe_le_coe]
      rw [← hQF_Ltilde p hp, ← hQF_Ltilde q hq,
        ← hQF_Ltilde (upperShift p q a) huK, ← hQF_Ltilde (lowerShift p q a) hvK]
      let u := upperShift p q a
      let v := lowerShift p q a
      obtain ⟨hsum, hdiff⟩ := shifted_pair_shape p q a
      have hrow : (∑ i, rowSum Ltilde i * ((u - v) i) ^ 2) ≤
          ∑ i, rowSum Ltilde i * ((p - q) i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [hdiff i]
        exact mul_le_mul_of_nonneg_left (reflection_square a _ ha) (hRow_Ltilde i)
      have hedge : (∑ i, ∑ j, Ltilde i j * ((p - q) i - (p - q) j) ^ 2) ≤
          ∑ i, ∑ j, Ltilde i j * ((u - v) i - (u - v) j) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : CharVec i - CharVec j ∈ S₀
        · have hpij : (p - q) i - (p - q) j = 0 := by
            simp [hK_eq_of_rel p hp i j hij, hK_eq_of_rel q hq i j hij]
          have huij : (u - v) i - (u - v) j = 0 := by
            simp [hK_eq_of_rel u huK i j hij, hK_eq_of_rel v hvK i j hij]
          rw [hpij, huij]
        · have hle_sq : ((u - v) i - (u - v) j) ^ 2 ≤ ((p - q) i - (p - q) j) ^ 2 := by
            rw [hdiff i, hdiff j]
            exact reflection_edge_square a _ _
          exact mul_le_mul_of_nonpos_left hle_sq (hOff_Ltilde i j hij)
      have hmono : QF Ltilde (u - v) ≤ QF Ltilde (p - q) := by
        rw [energy_decomposition Ltilde hLtilde_symm (u - v),
          energy_decomposition Ltilde hLtilde_symm (p - q)]
        linarith
      rw [qf_parallelogram Ltilde hLtilde_symm u v,
        qf_parallelogram Ltilde hLtilde_symm p q, hsum]
      linarith
    · simp [GenQF, hq]
  · simp [GenQF, hp]

end GenQFConjugacy

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (L M : Matrix V V ℝ) (K Hs : Set (V → ℝ)) (hLsymm : L.IsSymm) (hMsymm : M.IsSymm)
    (hLpsd : L.PosSemidef) (hMpsd : M.PosSemidef)
    (hK : K = OrthComp (Hs ∩ KerMat M)) (hH : Hs = OrthComp (K ∩ KerMat L))
    (hconj : (∀ p : V → ℝ, ConjugateWT (GenQF M Hs) p = ToEReal2 (GenQF L K p)) ∧
      (∀ x : V → ℝ, ConjugateWT (GenQF L K) x = ToEReal2 (GenQF M Hs x))) :
    TranslationSubmodularWT (GenQF L K) ↔ MNatExchangeWT (GenQF M Hs) := by
  rw [GenQFConjugacy.mnatExchangeWT_iff_condCPlusGen M Hs hMsymm hMpsd (K ∩ KerMat L) hH]
  exact ⟨GenQFConjugacy.condCPlusGen_of_translationSubmodularWT L M K Hs
      hLsymm hMsymm hLpsd hMpsd hK hH hconj,
    GenQFConjugacy.translationSubmodularWT_of_condCPlusGen L M K Hs
      hLsymm hMsymm hLpsd hMpsd hK hH hconj⟩



