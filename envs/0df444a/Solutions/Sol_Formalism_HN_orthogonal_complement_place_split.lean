-- Prove2me | solution 1 for Formalism.HN.orthogonal_complement_place_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:10.815124+00:00
-- url     : https://prove2.me/submissions/3e2faa62-1089-4f66-9213-6fcdf459387d

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Theorems.Thm_Formalism_HN_exists_decomp_of_mem_iSup
import Theorems.Thm_Formalism_HN_inner_zero_of_orthogonal_parts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution {P E : Type*} [Fintype P] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ev : P → Submodule ℝ E) (hEv : ∀ v w, v ≠ w → ∀ x ∈ Ev v, ∀ y ∈ Ev w, inner ℝ x y = 0)
    (S T : Submodule ℝ E) (hS : S = ⨆ v, S ⊓ Ev v) (hT : T = ⨆ v, T ⊓ Ev v) (hTS : T ≤ S) :
    S ⊓ Tᗮ = (⨆ v, S ⊓ Tᗮ ⊓ Ev v) ∧
    ∀ v, finrank ℝ (S ⊓ Tᗮ ⊓ Ev v : Submodule ℝ E) + finrank ℝ (T ⊓ Ev v : Submodule ℝ E) =
      finrank ℝ (S ⊓ Ev v : Submodule ℝ E) := by
  classical
  have key : ∀ v, S ⊓ Tᗮ ⊓ Ev v = S ⊓ Ev v ⊓ (T ⊓ Ev v)ᗮ := by
    intro v
    ext x
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨⟨hxS, hxT⟩, hxv⟩
      refine ⟨⟨hxS, hxv⟩, ?_⟩
      rw [Submodule.mem_orthogonal]
      intro u hu
      exact (Submodule.mem_orthogonal T x).1 hxT u hu.1
    · rintro ⟨⟨hxS, hxv⟩, hx⟩
      refine ⟨⟨hxS, ?_⟩, hxv⟩
      rw [Submodule.mem_orthogonal]
      exact inner_zero_of_orthogonal_parts Ev hEv T hT hxv
        (fun t ht => (Submodule.mem_orthogonal _ x).1 hx t ht)
  refine ⟨?_, fun v => ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨hxS, hxT⟩ := Submodule.mem_inf.1 hx
      rw [hS] at hxS
      obtain ⟨f, hf, rfl⟩ := exists_decomp_of_mem_iSup (fun w => S ⊓ Ev w) hxS
      refine Submodule.sum_mem _ fun w _ => Submodule.mem_iSup_of_mem w ?_
      rw [key w]
      refine Submodule.mem_inf.2 ⟨hf w, ?_⟩
      rw [Submodule.mem_orthogonal]
      intro t ht
      have h0 : inner ℝ t (∑ u, f u) = 0 := (Submodule.mem_orthogonal T _).1 hxT t ht.1
      rw [inner_sum, Finset.sum_eq_single w] at h0
      · exact h0
      · intro u _ hu
        exact hEv w u (Ne.symm hu) t ht.2 (f u) (hf u).2
      · intro h
        exact absurd (Finset.mem_univ w) h
    · exact iSup_le fun w => inf_le_left
  · have h := Submodule.finrank_add_inf_finrank_orthogonal (inf_le_inf_right (Ev v) hTS)
    rw [key v, inf_comm (S ⊓ Ev v)]
    omega
end Formalism.HN
