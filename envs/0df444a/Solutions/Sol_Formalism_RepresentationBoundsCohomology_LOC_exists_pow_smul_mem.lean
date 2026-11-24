-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.exists_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:46:38.78695+00:00
-- url     : https://prove2.me/submissions/aa98dccb-d099-4ffc-b982-b71c734ddcb9

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_StatDualFibreLattice
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_ExistsPowSmulIntegral
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_exists_pow_smul_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution {V : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] {T : Submodule O V}
    (hT : Submodule.span (FractionRing O) (T : Set V) = ⊤) {ϖ : O} (hϖ : Irreducible ϖ) (x : V) :
    ∃ n : ℕ, (ϖ ^ n) • x ∈ T := by
  have hx : x ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact T.smul_mem _ hn
    · rw [pow_add, mul_smul]; exact T.smul_mem _ hm
  | smul k x _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, a, ha⟩ := exists_pow_smul_integral hϖ k
    refine ⟨m + n, ?_⟩
    have : (ϖ ^ (m + n)) • k • x = a • (ϖ ^ n) • x := by
      rw [pow_add, mul_comm, mul_smul, ← smul_assoc (ϖ ^ m) k x, ha, algebraMap_smul,
        smul_comm]
    rw [this]; exact T.smul_mem _ hn
end Formalism.RepresentationBoundsCohomology.LOC
