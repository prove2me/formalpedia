-- Prove2me | solution 1 for Formalism.UG.P.afsplit_eps_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:37:01.665019+00:00
-- url     : https://prove2.me/submissions/bc72ea91-26b6-4a94-a03f-b3ee703ad9fc

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
section Lat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
end Lat
section Int
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
private lemma F_int_lemma_9 (y : v.adicCompletion F) (hy : y ∈ v.adicCompletionIntegers F) :
    afsplitF v y ∈ intAd F := by
  show ∀ w, (afsplitF v y) w ∈ w.adicCompletionIntegers F
  intro w
  by_cases h : w = v
  · subst h
    rw [afsplitF_self]
    exact hy
  · rw [afsplitF_ne v w h]
    exact zero_mem _
variable {n : Type} [Fintype n] [DecidableEq n]
end Int
section Iso
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
end Iso
end Formalism.UG.P
end
end

set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution : afsplitEps E v ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  unfold tensInt
  rw [eps_eq_lemma_2]
  exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨afsplitF v 1, F_int_lemma_9 v 1 (one_mem _)⟩, rfl⟩)
end Formalism.UG.P
