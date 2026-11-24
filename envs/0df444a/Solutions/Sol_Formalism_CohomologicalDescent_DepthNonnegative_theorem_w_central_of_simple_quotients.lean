-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.theorem_w_central_of_simple_quotients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:59.828503+00:00
-- url     : https://prove2.me/submissions/375e7913-7d59-4465-9496-571cbdc89f67

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_tensor_weight_kill_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_chain_monotone_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_chain_ends_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_factorAction_id
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_forms_induction_holds
import Theorems.Thm_Formalism_CohomologicalDescent_DepthNonnegative_forms_devissage_holds
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_RankGapBounds_FormsTensorLocalization_tensor_reduction_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution (hSS : SimpleSubquotOfPower) (hIso : SubquotIso) : TheoremWCore := by
  intro O _ A _ _ G _ Γ K jK ι _ _ Nb _ _ B _ _ T _ _ _ _ S l ϖ n₀ ω pr e Λ L _ _ _ _ _ hwt depth i T2
    ex c' hNoe hArt hdvd hstab he hHS hHN hclass hhw hIN1 hex hIN2
  let DA : Finset ι → Submodule A (⨂[O] τ, Nb τ) := fun s =>
    { toAddSubmonoid := (tensSub (chainB B s)).toAddSubmonoid
      smul_mem' := fun a x hx => hstab s a x hx }
  have hDA : ∀ s x, x ∈ DA s ↔ x ∈ tensSub (chainB B s) := fun s x => Iff.rfl
  have hends := chain_ends_holds O ι Nb B
  have hmono : ∀ s s' : Finset ι, s ⊆ s' → DA s ≤ DA s' := fun s s' h x hx =>
    chain_monotone_holds O ι Nb B s s' h hx
  have hval : ∀ (c : ℕ) (f : Forms O Γ jK (⨂[O] τ, Nb τ)) (g : G),
      (((algebraMap O T l) ^ c • f : Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g =
        l ^ c • (f : G → ⨂[O] τ, Nb τ) g := by
    intro c f g
    rw [← map_pow, algebraMap_smul]
    rfl
  have hpow : scaleSub A (⨂[O] τ, Nb τ) (ϖ ^ (n₀ * ∑ τ, ex τ)) ≤ DA ∅ := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨u, hu⟩ := hdvd
    rw [hDA, hends.1, pow_mul, hu, mul_pow, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (tensor_reduction_holds O ι Nb B l ex hex y)
  have hstep : ∀ (s : Finset ι) (a : ι), a ∉ s → ∀ f : Forms O Γ jK (⨂[O] τ, Nb τ),
      (∀ g, (f : G → ⨂[O] τ, Nb τ) g ∈ DA (insert a s)) →
      ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ cTau T2 ex c' a • f) :
        Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA s := by
    intro s a ha f hf
    have hkill : ∀ c : ℕ, (∀ x : Nb a, l ^ c • x ∈ B a) →
        ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ c • f) :
          Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA s := by
      intro c hc
      refine ⟨1, S.one_mem, fun g => ?_⟩
      rw [one_smul, hval]
      have h1 := tensor_weight_kill_holds O ι Nb B s a LinearMap.id l c ha hc _ (hf g)
      rwa [factorAction_id] at h1
    by_cases haT : a ∈ T2
    swap
    · have hc : cTau T2 ex c' a = ex a := by simp [cTau, haT]
      rw [hc]
      exact hkill _ (hex a)
    by_cases hle : ex a ≤ c' a
    · have hc : cTau T2 ex c' a = ex a := by simp [cTau, haT, hle]
      rw [hc]
      exact hkill _ (hex a)
    have hc : cTau T2 ex c' a = c' a := by
      simp only [cTau, haT, if_true]
      omega
    rw [hc]
    let E : Submodule A (⨂[O] τ, Nb τ) :=
      { carrier := {x | ∃ d ∈ DA s, ∃ n ∈ DA (insert a s), x = d + l ^ c' a • n}
        zero_mem' := ⟨0, (DA s).zero_mem, 0, (DA _).zero_mem, by simp⟩
        add_mem' := by
          rintro _ _ ⟨d, hd, n, hn, rfl⟩ ⟨d', hd', n', hn', rfl⟩
          exact ⟨d + d', (DA s).add_mem hd hd', n + n', (DA _).add_mem hn hn', by
            rw [smul_add]; abel⟩
        smul_mem' := by
          rintro b _ ⟨d, hd, n, hn, rfl⟩
          exact ⟨b • d, (DA s).smul_mem b hd, b • n, (DA _).smul_mem b hn, by
            rw [smul_add, smul_comm]⟩ }
    have hDE : DA s ≤ E := fun d hd => ⟨d, hd, 0, (DA _).zero_mem, by simp⟩
    have hD0 : tensSub B ≤ (DA s).restrictScalars O := by
      intro x hx
      rw [← hends.1] at hx
      exact hmono ∅ s (Finset.empty_subset _) hx
    refine forms_devissage_holds O A G Γ K jK T (⨂[O] τ, Nb τ) S (tensSub B) (DA s) E hNoe hArt hD0 hDE
      ?_ _ (fun g => ⟨0, (DA s).zero_mem, _, hf g, by rw [hval, zero_add]⟩)
    intro F F' hDF hcov hF'E
    have hsimple : IsSimpleModule A (F' ⧸ F.comap F'.subtype) :=
      (covBy_iff_quot_is_simple hcov.le).mp hcov
    have hsq := hSS O A (⨂[O] τ, Nb τ) ϖ _ F F' hcov.le
      (hpow.trans ((hmono ∅ s (Finset.empty_subset _)).trans hDF)) hsimple
    obtain ⟨μ, ⟨iso⟩⟩ := hclass _ hsimple hsq
    have hcf := hIso A _ _ (L μ) ⟨iso⟩ hsq
    let ψ : F' →ₗ[A] L μ := iso.toLinearMap.comp (F.comap F'.subtype).mkQ
    have hψ0 : ∀ x : F', (x : ⨂[O] τ, Nb τ) ∈ F → ψ x = 0 := by
      intro x hx
      show iso ((F.comap F'.subtype).mkQ x) = 0
      have h1 : (F.comap F'.subtype).mkQ x = 0 := by
        rw [Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero _).mpr (show x ∈ F.comap F'.subtype from hx)
      rw [h1, map_zero]
    have hker : ∀ x : F', ψ x = 0 → (x : ⨂[O] τ, Nb τ) ∈ F := by
      intro x hx
      have h1 : (F.comap F'.subtype).mkQ x = 0 := iso.injective (by rw [map_zero]; exact hx)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    have hdeep : i a < depth a (hwt μ a) := by
      by_contra hnot
      have hle' : depth a (hwt μ a) ≤ i a := not_lt.mp hnot
      obtain ⟨z, hz⟩ := hhw μ a
      obtain ⟨x, rfl⟩ : ∃ x, ψ x = z :=
        (iso.surjective.comp (Submodule.mkQ_surjective _)) z
      apply hz
      rw [← map_smul]
      apply hψ0
      obtain ⟨d, hd, n, hn, hxe⟩ := hF'E x.2
      rw [Submodule.coe_smul, hxe, smul_add, smul_comm]
      refine F.add_mem (hDF ((DA s).smul_mem _ hd)) (hDF ?_)
      rw [he]
      exact tensor_weight_kill_holds O ι Nb B s a (pr a (hwt μ a)) l (c' a) ha
        (hIN2 a haT _ hle') n hn
    have hvan : Subsingleton (LocalizedModule S (Forms O Γ jK (L μ))) := by
      by_contra hns
      exact absurd (hIN1 μ hcf hns a haT) (not_le.mpr hdeep)
    exact forms_induction_holds O A G Γ K jK T (⨂[O] τ, Nb τ) (L μ) S F F' ψ hHS (hHN μ) hker hvan
  have hall : ∀ s : Finset ι, ∀ f : Forms O Γ jK (⨂[O] τ, Nb τ),
      (∀ g, (f : G → ⨂[O] τ, Nb τ) g ∈ DA s) →
      ∃ σ ∈ S, ∀ g, ((σ • ((algebraMap O T l) ^ (∑ τ ∈ s, cTau T2 ex c' τ) • f) :
        Forms O Γ jK (⨂[O] τ, Nb τ)) : G → ⨂[O] τ, Nb τ) g ∈ DA ∅ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      exact ⟨1, S.one_mem, by simpa using hf⟩
    | insert a s ha ih =>
      intro f hf
      obtain ⟨σ1, hσ1, h1⟩ := hstep s a ha f hf
      obtain ⟨σ2, hσ2, h2⟩ := ih _ h1
      refine ⟨σ2 * σ1, S.mul_mem hσ2 hσ1, fun g => ?_⟩
      have e1 : (σ2 * σ1) • ((algebraMap O T l) ^ (∑ τ ∈ insert a s, cTau T2 ex c' τ) • f) =
          σ2 • ((algebraMap O T l) ^ (∑ τ ∈ s, cTau T2 ex c' τ) •
            (σ1 • ((algebraMap O T l) ^ cTau T2 ex c' a • f))) := by
        rw [Finset.sum_insert ha]
        simp only [smul_smul]
        congr 1
        ring
      rw [e1]
      exact h2 g
  intro y
  induction y using LocalizedModule.induction_on with
  | h f σ0 =>
    obtain ⟨σ, hσ, h⟩ := hall Finset.univ f (fun g => by rw [hDA, hends.2]; trivial)
    refine ⟨σ • ((algebraMap O T l) ^ (∑ τ, cTau T2 ex c' τ) • f), ?_, ⟨σ, hσ⟩ * σ0, ?_⟩
    · refine ⟨Subtype.property _, fun g _ => ?_⟩
      have h1 := h g
      rwa [hDA, hends.1] at h1
    · rw [LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel_common_left ⟨σ, hσ⟩ σ0 _
end Formalism.CohomologicalDescent.DepthNonnegative
