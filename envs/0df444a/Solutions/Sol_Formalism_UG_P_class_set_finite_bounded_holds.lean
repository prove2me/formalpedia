-- Prove2me | solution 1 for Formalism.UG.P.class_set_finite_bounded_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:12.805057+00:00
-- url     : https://prove2.me/submissions/37ff86fe-a7f8-497e-9a46-499a4b3d3e9b

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ShortVectors
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomOfTrace
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_ClassSetFiniteBoundedHolds
import Theorems.Thm_Formalism_UG_P_csBdd_nat_mul
import Theorems.Thm_Formalism_HermitianLatticesTheory_classSetFinite_core
import Theorems.Thm_Formalism_HermitianLatticesTheory_finIntermediate
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomOfTrace
import Theorems.Thm_Formalism_HermitianLatticesTheory_shortVectors
import Theorems.Thm_Formalism_HermitianLatticesTheory_traceReal_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution (hCovolOfDual : Formalism.UG.CS.CovolOfDual) :
    Formalism.UG.CS.ClassSetFiniteBdd := by
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos d e hd he
  obtain ⟨N, ι, hι, hmul, hlat⟩ := Formalism.HermitianLatticesTheory.traceReal_main h hsymm hpos
  obtain ⟨C, hC⟩ := hCovolOfDual K V h hsymm hpos N ι hι e he
  obtain ⟨m, hm, t, ht⟩ := csBdd_nat_mul d hd
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (𝓞 K) K)) ∧
    (∀ x ∈ Formalism.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M)}
  have hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M, (m : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro M hM x hx y hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hM.2.1 x hx y hy)
    refine Submodule.mem_one.mpr ⟨t * a, ?_⟩
    have hmK : (m : K) = (d : K) * (t : K) := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      simpa using this
    rw [map_mul, ha, hmK]
    have htc : algebraMap (𝓞 K) K t = (t : K) := rfl
    rw [htc]
    ring
  obtain ⟨s, -, hs⟩ := Formalism.HermitianLatticesTheory.classSetFinite_core Formalism.HermitianLatticesTheory.shortVectors
    Formalism.HermitianLatticesTheory.finIntermediate Formalism.HermitianLatticesTheory.isomOfTrace h hpos N ι hι hmul m hm C S hSd
    (fun M hM => hlat M hM.1) (fun M hM _ _ => hC M hM.1 hM.2.2)
  exact ⟨s, fun M hM hdM heM => hs M ⟨hM, hdM, heM⟩⟩
end Formalism.UG.P
