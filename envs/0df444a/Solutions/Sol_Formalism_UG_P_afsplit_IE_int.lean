-- Prove2me | solution 1 for Formalism.UG.P.afsplit_IE_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:37:00.717799+00:00
-- url     : https://prove2.me/submissions/88c6a822-4ad6-486e-af7a-af0e147a44f8

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
theorem _root_.solution (x : E ⊗[F] v.adicCompletion F)
    (hx : x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) :
    afsplitIE v x ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F) := by
  unfold tensInt at hx ⊢
  induction hx using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have h1 : afsplitIE v ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F)) =
          ((a : E) ⊗ₜ[F] (1 : 𝔸)) * ((1 : E) ⊗ₜ[F] afsplitF v 1) := by
        rw [IE_tmul_lemma_10, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      simp only [h1]
      exact mul_mem (Subring.subset_closure (Set.mem_union_left _ ⟨a, rfl⟩))
        (Subring.subset_closure (Set.mem_union_right _ ⟨⟨afsplitF v 1, F_int_lemma_9 v 1 (one_mem _)⟩, rfl⟩))
    · show afsplitIE v ((1 : E) ⊗ₜ[F] ((b : v.adicCompletion F))) ∈ _
      rw [IE_tmul_lemma_10]
      exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨afsplitF v b, F_int_lemma_9 v b b.2⟩, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | one =>
    rw [show afsplitIE v 1 = afsplitEps E v from rfl, eps_eq_lemma_2]
    exact Subring.subset_closure (Set.mem_union_right _ ⟨⟨afsplitF v 1, F_int_lemma_9 v 1 (one_mem _)⟩, rfl⟩)
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
end Formalism.UG.P
