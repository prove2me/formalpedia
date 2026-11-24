-- Prove2me | solution 1 for Formalism.UG.P.afsplitE_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:14:05.778121+00:00
-- url     : https://prove2.me/submissions/d49bfba5-097a-4266-8176-096823576410

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Theorems.Thm_Formalism_UG_P_afsplit_stab_iff
import Theorems.Thm_Formalism_UG_P_afsplit_one_mem
import Theorems.Thm_Formalism_UG_P_afsplit_prV_int
import Theorems.Thm_Formalism_UG_P_afsplitC_int
import Theorems.Thm_Formalism_UG_P_afsplitE_symm
import Theorems.Thm_Formalism_UG_P_afsplitU_mem


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
  {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution :
    ((levelAf σ J).subgroupOf (UPts σ J 𝔸)).map (afsplitE σ J v).toMonoidHom =
      ((levelV σ J v).subgroupOf (UPts σ J (v.adicCompletion F))).prod
        ((levelAf σ J).subgroupOf (afsplitKer σ J v)) := by
  have hAf : ∀ x : GL n (E ⊗[F] 𝔸), x ∈ levelAf σ J ↔ x ∈ UPts σ J 𝔸 ∧
      ((∀ i j, (x : Matrix n n (E ⊗[F] 𝔸)) i j ∈ tensInt (F := F) 𝔸 (intOE E) (intAd F)) ∧
       (∀ i j, ((x⁻¹ : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) i j ∈
          tensInt (F := F) 𝔸 (intOE E) (intAd F))) :=
    fun x => Subgroup.mem_inf.trans (and_congr Iff.rfl (afsplit_stab_iff _ x))
  have hV : ∀ x : GL n (E ⊗[F] v.adicCompletion F), x ∈ levelV σ J v ↔
      x ∈ UPts σ J (v.adicCompletion F) ∧
      ((∀ i j, (x : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) ∧
       (∀ i j, ((x⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈
          tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring)) :=
    fun x => Subgroup.mem_inf.trans (and_congr Iff.rfl (afsplit_stab_iff _ x))
  ext p
  obtain ⟨⟨h, hh⟩, ⟨k, hk⟩⟩ := p
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_prod, Subgroup.mem_subgroupOf, afsplitE_symm]
  rw [hAf, hV, hAf]
  have hkU := (Subgroup.mem_inf.mp hk).1
  have h1mem : ∀ i j, (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring :=
    fun i j => afsplit_one_mem _ i j
  constructor
  · rintro ⟨-, hC, hCi⟩
    have hki : k⁻¹ ∈ afsplitKer σ J v := inv_mem hk
    have eh : ∀ i j, prV (E := E) v (afsplitC v (h : Matrix n n (E ⊗[F] v.adicCompletion F))
        (k : Matrix n n (E ⊗[F] 𝔸)) i j) = (h : Matrix n n (E ⊗[F] v.adicCompletion F)) i j :=
      fun i j => congrFun (congrFun (C_map_prV_lemma_5 v (h : Matrix n n (E ⊗[F] v.adicCompletion F))
        (k : Matrix n n (E ⊗[F] 𝔸))) i) j
    have ehi : ∀ i j, prV (E := E) v (afsplitC v ((h⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) ((k⁻¹ : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸)) i j) =
        ((h⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j :=
      fun i j => congrFun (congrFun (C_map_prV_lemma_5 v ((h⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) :
        Matrix n n (E ⊗[F] v.adicCompletion F)) ((k⁻¹ : GL n (E ⊗[F] 𝔸)) : Matrix n n (E ⊗[F] 𝔸))) i) j
    have ek : afsplitU v 1 (afsplitU v h k) = k := afsplit_right2 σ J v h k hk
    have eki : afsplitU v 1 (afsplitU v h⁻¹ k⁻¹) = k⁻¹ := afsplit_right2 σ J v h⁻¹ k⁻¹ hki
    refine ⟨⟨hh, fun i j => ?_, fun i j => ?_⟩, ⟨hkU, fun i j => ?_, fun i j => ?_⟩⟩
    · rw [← eh]
      exact afsplit_prV_int v _ (hC i j)
    · rw [← ehi]
      exact afsplit_prV_int v _ (hCi i j)
    · rw [← ek]
      exact afsplitC_int v _ _ h1mem hC i j
    · rw [← eki]
      exact afsplitC_int v _ _ h1mem hCi i j
  · rintro ⟨⟨-, hh1, hh2⟩, ⟨-, hk1, hk2⟩⟩
    exact ⟨afsplitU_mem v σ J h k hh hkU, fun i j => afsplitC_int v _ _ hh1 hk1 i j,
      fun i j => afsplitC_int v _ _ hh2 hk2 i j⟩
end Formalism.UG.P
