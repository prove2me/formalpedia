-- Prove2me | solution 1 for Formalism.UG.P.afsplit_prV_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:44.914819+00:00
-- url     : https://prove2.me/submissions/672d3272-af2d-4e88-b43c-993e52519e2b

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
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution (x : E ⊗[F] 𝔸) (hx : x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) :
    prV (E := E) v x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E)
      (v.adicCompletionIntegers F).toSubring := by
  unfold tensInt at hx ⊢
  induction hx using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · apply Subring.subset_closure
      refine Set.mem_union_left _ ⟨a, ?_⟩
      simp [prV_tmul_lemma_12]
      rfl
    · apply Subring.subset_closure
      refine Set.mem_union_right _ ⟨⟨(b : 𝔸) v, b.2 v⟩, ?_⟩
      simp [prV_tmul_lemma_12]
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
end Formalism.UG.P
