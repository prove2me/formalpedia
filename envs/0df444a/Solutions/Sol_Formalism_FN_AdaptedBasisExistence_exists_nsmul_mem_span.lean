-- Prove2me | solution 1 for Formalism.FN.AdaptedBasisExistence.exists_nsmul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:30.776171+00:00
-- url     : https://prove2.me/submissions/ba5e60f4-1147-4483-ba13-0e5106df8dc2

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_AdaptedBasis

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
namespace Formalism.FN.AdaptedBasisExistence
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {ι : Type} [Fintype ι]
    (B : Basis ι ℝ E) (hB : ∀ i, B i ∈ L) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, N • x ∈ span ℤ (Set.range B) := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  have hKL : span ℤ (Set.range B) ≤ L := by
    rw [span_le]
    rintro _ ⟨i, rfl⟩
    exact hB i
  have hdisc : IsDiscrete (L : Set E) := IsDiscrete.mk (inferInstance : DiscreteTopology L)
  haveI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hclosed : IsClosed (L : Set E) := AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  have hfin : (ZSpan.fundamentalDomain B ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed hdisc (ZSpan.fundamentalDomain_isBounded B) hclosed
  obtain ⟨S, hS⟩ : ∃ S : Finset E, ∀ y, y ∈ S ↔ y ∈ ZSpan.fundamentalDomain B ∩ (L : Set E) :=
    ⟨hfin.toFinset, fun y => hfin.mem_toFinset⟩
  refine ⟨S.card.factorial, Nat.factorial_pos _, fun x hx => ?_⟩
  have hmem : ∀ k : ℕ, ZSpan.fract B (k • x) ∈ S := by
    intro k
    rw [hS]
    refine ⟨ZSpan.fract_mem_fundamentalDomain B _, ?_⟩
    rw [ZSpan.fract_apply]
    exact L.sub_mem (nsmul_mem hx k) (hKL (ZSpan.floor B (k • x)).2)
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (S.card + 1) => (⟨ZSpan.fract B ((k : ℕ) • x), hmem k⟩ : S)) (by simp)
  have heq' : ZSpan.fract B ((a : ℕ) • x) = ZSpan.fract B ((b : ℕ) • x) :=
    congrArg Subtype.val heq
  rw [ZSpan.fract_eq_fract] at heq'
  have hab' : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  have key : ∃ k : ℕ, 0 < k ∧ k ≤ S.card ∧ k • x ∈ span ℤ (Set.range B) := by
    rcases lt_or_gt_of_ne hab' with h | h
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt h
      refine ⟨c + 1, Nat.succ_pos _, by omega, ?_⟩
      have e : -((a : ℕ) • x) + (b : ℕ) • x = (c + 1) • x := by
        rw [hc, add_assoc, add_nsmul]
        abel
      rw [← e]
      exact heq'
    · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt h
      refine ⟨c + 1, Nat.succ_pos _, by omega, ?_⟩
      have e : -(-((a : ℕ) • x) + (b : ℕ) • x) = (c + 1) • x := by
        rw [hc, add_assoc, add_nsmul]
        abel
      rw [← e]
      exact neg_mem heq'
  obtain ⟨k, hk0, hkS, hkx⟩ := key
  obtain ⟨d, hd⟩ := Nat.dvd_factorial hk0 hkS
  rw [hd, mul_comm, ← smul_smul]
  exact nsmul_mem hkx d
end Formalism.FN.AdaptedBasisExistence
