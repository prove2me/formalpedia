-- Prove2me | solution 1 for Formalism.L2.Pj.AvAlg.adjoin_residue_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:14:12.548522+00:00
-- url     : https://prove2.me/submissions/06a0ca7c-144f-41d8-9235-7a6d77c7789c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.AvAlg
variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
namespace Formalism.L2.Pj.AvAlg
theorem _root_.solution [Finite (ResidueField B)] :
    ∃ γ : ResidueField B, Algebra.adjoin (ResidueField A) {γ} = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ResidueField B)ˣ)
  refine ⟨(g : ResidueField B), ?_⟩
  rw [eq_top_iff]
  intro x _
  by_cases hx : x = 0
  · rw [hx]; exact Subalgebra.zero_mem _
  · obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 x hx)))
    have e : x = (g : ResidueField B) ^ n := by
      rw [← Units.val_pow_eq_pow_val, show g ^ n = Units.mk0 x hx from hn, Units.val_mk0]
    rw [e]
    exact Subalgebra.pow_mem (Algebra.adjoin (ResidueField A) {(g : ResidueField B)})
      (Algebra.subset_adjoin (Set.mem_singleton _)) n
end Formalism.L2.Pj.AvAlg
