-- Prove2me | solution 1 for Formalism.FN.AdaptedBasisExistence.adapted_basis_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:43.660686+00:00
-- url     : https://prove2.me/submissions/3efdf4fd-fae0-4896-9d89-faf7d8d670e6

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_AdaptedBasis
import Theorems.Thm_Formalism_FN_AdaptedBasisExistence_exists_nsmul_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.FN Formalism.FN.AdaptedBasisExistence
set_option maxHeartbeats 800000
namespace Formalism.FN.AdaptedBasisExistence
theorem _root_.solution : AdaptedBasis := by
  delta Formalism.FN.AdaptedBasis
  intro E _ _ _ L _ _ v hv hvL
  classical
  have hsp0 : ⊤ ≤ span ℝ (Set.range v) :=
    (hv.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)).ge
  let B : Basis (Fin (finrank ℝ E)) ℝ E := Basis.mk hv hsp0
  have hBv : ∀ i, B i = v i := fun i => congrFun (Basis.coe_mk hv hsp0) i
  obtain ⟨N, hN, hNL⟩ := exists_nsmul_mem_span L B (fun i => by rw [hBv]; exact hvL i)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hint : ∀ x ∈ L, ∀ k, ∃ z : ℤ, (N : ℝ) * B.repr x k = z := by
    intro x hx k
    obtain ⟨z, hz⟩ := (Basis.mem_span_iff_repr_mem ℤ B (N • x)).mp (hNL x hx) k
    have hz' : (z : ℝ) = (N : ℝ) * B.repr x k := by simpa using hz
    exact ⟨z, hz'.symm⟩
  have hP : ∀ j : Fin (finrank ℝ E), ∃ m : ℕ, 0 < m ∧ ∃ x, (x ∈ L ∧ ∀ k, j < k → B.repr x k = 0) ∧
      (N : ℝ) * B.repr x j = m := by
    intro j
    refine ⟨N, hN, v j, ⟨hvL j, fun k hk => ?_⟩, ?_⟩
    · rw [← hBv, B.repr_self, Finsupp.single_apply, if_neg (ne_of_lt hk)]
    · rw [← hBv, B.repr_self, Finsupp.single_apply, if_pos rfl, mul_one]
  have hm := fun j => Nat.find_spec (hP j)
  have hmin := fun j (r : ℕ) (hr : r < Nat.find (hP j)) => Nat.find_min (hP j) hr
  choose b hbG hbj using fun j => (hm j).2
  have hdiv : ∀ j x, (x ∈ L ∧ ∀ k, j < k → B.repr x k = 0) →
      ∃ q : ℤ, B.repr x j = q * B.repr (b j) j := by
    intro j x hx
    obtain ⟨z, hz⟩ := hint x hx.1 j
    have hmpos : 0 < (Nat.find (hP j) : ℤ) := by exact_mod_cast (hm j).1
    have hr0 : 0 ≤ z % (Nat.find (hP j) : ℤ) := Int.emod_nonneg _ hmpos.ne'
    have hrlt : z % (Nat.find (hP j) : ℤ) < Nat.find (hP j) := Int.emod_lt_of_pos _ hmpos
    have hcast : ((z % (Nat.find (hP j) : ℤ) : ℤ) : ℝ) =
        (z : ℝ) - ((z / (Nat.find (hP j) : ℤ) : ℤ) : ℝ) * (Nat.find (hP j) : ℝ) := by
      have h := congrArg (fun t : ℤ => (t : ℝ)) (Int.ediv_mul_add_emod z (Nat.find (hP j) : ℤ))
      push_cast at h
      linarith
    by_cases hr : z % (Nat.find (hP j) : ℤ) = 0
    · refine ⟨z / (Nat.find (hP j) : ℤ), ?_⟩
      apply mul_left_cancel₀ hN'
      rw [hz, mul_left_comm, hbj]
      rw [hr] at hcast
      push_cast at hcast
      linarith
    · exfalso
      have hrpos : 0 < z % (Nat.find (hP j) : ℤ) := lt_of_le_of_ne hr0 (Ne.symm hr)
      have e : ∀ k, B.repr (x - (z / (Nat.find (hP j) : ℤ)) • b j) k =
          B.repr x k - ((z / (Nat.find (hP j) : ℤ) : ℤ) : ℝ) * B.repr (b j) k := by
        intro k
        simp
      refine hmin j (z % (Nat.find (hP j) : ℤ)).toNat (by omega)
        ⟨by omega, x - (z / (Nat.find (hP j) : ℤ)) • b j,
          ⟨L.sub_mem hx.1 (L.smul_mem _ (hbG j).1), fun k hk => ?_⟩, ?_⟩
      · rw [e, hx.2 k hk, (hbG j).2 k hk, mul_zero, sub_zero]
      · rw [e, mul_sub, mul_left_comm, hbj, hz]
        have h2 : (((z % (Nat.find (hP j) : ℤ)).toNat : ℕ) : ℝ) =
            ((z % (Nat.find (hP j) : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg hr0
        rw [h2, hcast]
  have hspan : ∀ r : ℕ, ∀ x ∈ L, (∀ k : Fin (finrank ℝ E), r ≤ k.val → B.repr x k = 0) →
      x ∈ span ℤ (b '' {k | k.val < r}) := by
    intro r
    induction r with
    | zero =>
      intro x _ h0
      have hx0 : x = 0 := B.repr.injective (by ext k; simp [h0 k (Nat.zero_le _)])
      rw [hx0]
      exact zero_mem _
    | succ r ih =>
      intro x hx h
      by_cases hr : r < finrank ℝ E
      · obtain ⟨q, hq⟩ := hdiv ⟨r, hr⟩ x ⟨hx, fun k hk => h k (by rw [Fin.lt_def] at hk; exact hk)⟩
        have e : ∀ k, B.repr (x - q • b ⟨r, hr⟩) k = B.repr x k - (q : ℝ) * B.repr (b ⟨r, hr⟩) k := by
          intro k
          simp
        have hy : x - q • b ⟨r, hr⟩ ∈ span ℤ (b '' {k | k.val < r}) := by
          refine ih _ (L.sub_mem hx (L.smul_mem q (hbG _).1)) fun k hk => ?_
          rw [e]
          rcases Nat.lt_or_ge r k.val with hk' | hk'
          · rw [h k hk', (hbG _).2 k (by rw [Fin.lt_def]; exact hk'), mul_zero, sub_zero]
          · have hkr : k = ⟨r, hr⟩ := Fin.ext (show k.val = r by omega)
            rw [hkr, hq, sub_self]
        have hb_mem : b ⟨r, hr⟩ ∈ span ℤ (b '' {k | k.val < r + 1}) :=
          subset_span ⟨⟨r, hr⟩, by simp, rfl⟩
        have hmono : span ℤ (b '' {k | k.val < r}) ≤ span ℤ (b '' {k | k.val < r + 1}) :=
          span_mono (Set.image_mono fun k (hk : k.val < r) => show k.val < r + 1 by omega)
        have hsum := add_mem (hmono hy) (smul_mem _ q hb_mem)
        rwa [sub_add_cancel] at hsum
      · have hmono : span ℤ (b '' {k | k.val < r}) ≤ span ℤ (b '' {k | k.val < r + 1}) :=
          span_mono (Set.image_mono fun k (hk : k.val < r) => show k.val < r + 1 by omega)
        exact hmono (ih x hx fun k hk => absurd k.isLt (by omega))
  have hbL : ∀ j, b j ∈ L := fun j => (hbG j).1
  have hall : ∀ x ∈ L, x ∈ span ℤ (Set.range b) := fun x hx =>
    span_mono (Set.image_subset_range _ _)
      (hspan (finrank ℝ E) x hx fun k hk => absurd k.isLt (by omega))
  let b' : Fin (finrank ℝ E) → L := fun j => ⟨b j, hbL j⟩
  have hsp : ⊤ ≤ span ℤ (Set.range b') := by
    rintro x -
    have h2 := hall x x.2
    have h3 : Set.range b = L.subtype '' Set.range b' := by
      rw [← Set.range_comp]
      rfl
    rw [h3, ← Submodule.map_span, Submodule.mem_map] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    rwa [← Subtype.ext hyx]
  have hliR : LinearIndependent ℝ b := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (Fintype.card_fin _)
    refine le_trans hsp0 (span_le.mpr ?_)
    rintro _ ⟨i, rfl⟩
    exact span_le_restrictScalars ℤ ℝ _ (hall _ (hvL i))
  have hliZ : LinearIndependent ℤ b' :=
    LinearIndependent.of_comp L.subtype (hliR.restrict_scalars' ℤ)
  refine ⟨Basis.mk hliZ hsp, fun j => ?_⟩
  simp only [Basis.coe_mk]
  change span ℝ (b '' {k | k ≤ j}) = span ℝ (v '' {k | k ≤ j})
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [Set.mem_setOf_eq] at hk
    have hvB : v '' {k | k ≤ j} = B '' {k | k ≤ j} := Set.image_congr fun i _ => (hBv i).symm
    rw [SetLike.mem_coe, hvB, B.mem_span_image]
    intro i hi
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hi
    by_contra hij
    rw [Set.mem_setOf_eq, not_le] at hij
    exact hi ((hbG k).2 i (lt_of_le_of_lt hk hij))
  · rw [span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [Set.mem_setOf_eq] at hi
    have hvi := hspan (j.val + 1) (v i) (hvL i) fun k hk => by
      rw [← hBv, B.repr_self, Finsupp.single_apply, if_neg]
      intro hik
      rw [hik, Fin.le_def] at hi
      omega
    have hsub : {k : Fin (finrank ℝ E) | k.val < j.val + 1} ⊆ {k | k ≤ j} := by
      intro k hk
      simp only [Set.mem_setOf_eq] at hk ⊢
      rw [Fin.le_def]
      omega
    exact span_le_restrictScalars ℤ ℝ _ (span_mono (Set.image_mono hsub) hvi)
end Formalism.FN.AdaptedBasisExistence
