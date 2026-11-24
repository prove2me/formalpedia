-- Prove2me | solution 1 for Formalism.NG.matlis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:26.103314+00:00
-- url     : https://prove2.me/submissions/4e5ea6e7-f8ed-4922-90da-835225dd080f

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Theorems.Thm_Formalism_NG_IdempotentImageSmul_length_hom_quot
import Theorems.Thm_Formalism_NG_IdempotentImageSmul_length_self_top
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open IdempotentImageSmul
namespace Formalism.NG
theorem _root_.solution : StatMatlis := by
  classical
  intro O N _ _ _ _ _ hN
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hN
  have : IsNoetherian O N := hNA.1
  obtain ⟨n, ι, _, p, -, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum (R := O) (M := N)
  set A : ι → Type _ := fun i => O ⧸ O ∙ p i ^ e i with hA
  let g : (DirectSum ι A) ≃ₗ[O] (Π i, A i) := DirectSum.linearEquivFunOnFintype O ι A
  have hlenA : ∀ i, Module.length O (A i) = addVal O (p i ^ e i) := fun i =>
    IdempotentNormalFormsLenFacts.length_quot_span (p i ^ e i)
  have hlenH : ∀ i, Module.length O (A i →ₗ[O] KO O) = addVal O (p i ^ e i) := fun i =>
    length_hom_quot (p i ^ e i)
  have hN1 : Module.length O N =
      Module.length O (Fin n →₀ O) + ∑ i, addVal O (p i ^ e i) := by
    rw [f.length_eq, Module.length_prod, g.length_eq, Module.length_pi_of_fintype]
    simp only [hlenA]
  have hF : Module.length O (Fin n →₀ O) = 0 := by
    rw [Module.length_finsupp, length_self_top]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · exfalso
      have : Module.length O N = ⊤ := by
        rw [hN1, Module.length_finsupp, length_self_top, ENat.card_eq_coe_fintype_card,
          Fintype.card_fin, ENat.mul_top (by exact_mod_cast hn.ne'), top_add]
      exact (Module.length_ne_top_iff.mpr hN) this
  have : Subsingleton (Fin n →₀ O) := Module.length_eq_zero_iff.mp hF
  have hFH : Module.length O ((Fin n →₀ O) →ₗ[O] KO O) = 0 := by
    rw [Module.length_eq_zero_iff]
    exact ⟨fun φ ψ => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  let h1 : (N →ₗ[O] KO O) ≃ₗ[O] ((Fin n →₀ O) × DirectSum ι A →ₗ[O] KO O) :=
    f.arrowCongr (LinearEquiv.refl O (KO O))
  let h2 : (DirectSum ι A →ₗ[O] KO O) ≃ₗ[O] ((Π i, A i) →ₗ[O] KO O) :=
    g.arrowCongr (LinearEquiv.refl O (KO O))
  have h3 : Module.length O ((Π i, A i) →ₗ[O] KO O) = ∑ i, addVal O (p i ^ e i) := by
    have := (LinearMap.lsum O A O : (Π i, A i →ₗ[O] KO O) ≃ₗ[O] _).length_eq
    rw [← this, Module.length_pi_of_fintype]
    simp only [hlenH]
  rw [h1.length_eq, ← (LinearMap.coprodEquiv O).length_eq, Module.length_prod, h2.length_eq,
    h3, hFH, hN1, hF]
end Formalism.NG
