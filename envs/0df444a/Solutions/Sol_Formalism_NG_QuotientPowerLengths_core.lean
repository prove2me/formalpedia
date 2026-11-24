-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:36.284856+00:00
-- url     : https://prove2.me/submissions/961f5692-bb38-4ba2-8b57-62e8d84e397a

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_smulRange
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_quot_mono
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_step1
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_split
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_img_mono

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
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution {X : Type*} (E : Set (Module.End (FractionRing O) V))
    (W : X → Submodule (FractionRing O) V) (w : X → ℕ∞) (S : Finset X) :
    (∀ f ∈ E, ∀ x ∈ S, W x ≤ (W x).comap f) →
    (∀ x ∈ S, ∃ f ∈ E, ∃ l : O, (∀ v ∈ W x, f v = l • v) ∧ addVal O l ≤ w x) →
    ∀ U : Submodule (FractionRing O) V, (∀ f ∈ E, U ≤ U.comap f) →
    ∀ N : Submodule O V, N.FG → (∀ f ∈ E, ∀ n ∈ N, f n ∈ N) →
    N ≤ ((⨆ x ∈ S, W x) ⊔ U).restrictScalars O →
    Module.length O (N ⧸ Dsub E N U) ≤ ∑ x ∈ S, (finrank (FractionRing O) (W x) : ℕ∞) * w x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ U _ N _ _ hNU
    have htop : Dsub E N U = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨n, hn⟩ -
      have hnU : n ∈ U := by
        have h' : n ∈ (⨆ x ∈ (∅ : Finset X), W x) ⊔ U := hNU hn
        simpa using h'
      show n ∈ img E N ⊔ (U.restrictScalars O ⊓ N)
      exact Submodule.mem_sup_right (Submodule.mem_inf.mpr ⟨hnU, hn⟩)
    rw [htop, Finset.sum_empty]
    first
      | simp
      | exact (Module.length_eq_zero_iff.mpr inferInstance).le
      | exact le_of_eq (Module.length_eq_zero_iff.mpr ((Submodule.Quotient.subsingleton_iff _).mpr rfl))
  | @insert x S hxS ih =>
    intro h1 h2 U hU N hN hNE hNS
    obtain ⟨f, hfE, l, hfl, hlw⟩ := h2 x (Finset.mem_insert_self x S)
    obtain ⟨U₁, hU₁⟩ : ∃ U₁ : Submodule (FractionRing O) V, U₁ = (⨆ y ∈ S, W y) ⊔ U := ⟨_, rfl⟩
    have hEU₁ : ∀ g ∈ E, U₁ ≤ U₁.comap g := by
      intro g hg
      rw [hU₁]
      refine sup_le (iSup₂_le fun y hy => ?_) ?_
      · exact (h1 g hg y (Finset.mem_insert_of_mem hy)).trans
          (Submodule.comap_mono (le_sup_of_le_left (le_iSup₂_of_le y hy le_rfl)))
      · exact (hU g hg).trans (Submodule.comap_mono le_sup_right)
    have hNWU : N ≤ (W x ⊔ U₁).restrictScalars O := by
      have hle : (⨆ y ∈ insert x S, W y) ⊔ U ≤ W x ⊔ U₁ := by
        rw [hU₁]
        refine sup_le (iSup₂_le fun y hy => ?_) (le_sup_of_le_right le_sup_right)
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact le_sup_left
        · exact le_sup_of_le_right (le_sup_of_le_left (le_iSup₂_of_le y hy le_rfl))
      intro n hn
      have h : n ∈ (⨆ y ∈ insert x S, W y) ⊔ U := hNS hn
      exact hle h
    obtain ⟨N', hN'⟩ : ∃ N' : Submodule O V, N' = N ⊓ U₁.restrictScalars O := ⟨_, rfl⟩
    have hN'N : N' ≤ N := by rw [hN']; exact inf_le_left
    have hN'ge : N ⊓ U₁.restrictScalars O ≤ N' := hN'.ge
    have hN'U : N' ≤ U₁.restrictScalars O := by rw [hN']; exact inf_le_right
    have hN'fg : N'.FG := by
      haveI : IsNoetherian O N := isNoetherian_of_fg_of_noetherian N hN
      have hfg : (N'.comap N.subtype).FG := IsNoetherian.noetherian _
      have hmap := hfg.map N.subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN'N] at hmap
    have hN'E : ∀ g ∈ E, ∀ n ∈ N', g n ∈ N' := by
      intro g hg n hn
      have hn1 : n ∈ N := hN'N hn
      have hn2 : n ∈ U₁ := hN'U hn
      have hg2 : g n ∈ U₁ := hEU₁ g hg hn2
      exact hN'ge (Submodule.mem_inf.mpr ⟨hNE g hg n hn1, hg2⟩)
    have hN'S : N' ≤ ((⨆ y ∈ S, W y) ⊔ U).restrictScalars O := by
      rw [← hU₁]; exact hN'U
    have hih := ih (fun g hg y hy => h1 g hg y (Finset.mem_insert_of_mem hy))
      (fun y hy => h2 y (Finset.mem_insert_of_mem hy)) U hU N' hN'fg hN'E hN'S
    obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Submodule O N,
        B₀ = smulRange N l ⊔ LinearMap.ker ((U₁.mkQ.restrictScalars O) ∘ₗ N.subtype) := ⟨_, rfl⟩
    have hstep := step1 N hN (W x) U₁ hNWU l
    rw [← hB₀] at hstep
    have hiB : ∀ p : N', Submodule.inclusion hN'N p ∈ Dsub E N U ⊔ B₀ := by
      intro p
      rw [hB₀]
      refine Submodule.mem_sup_right (Submodule.mem_sup_right ?_)
      rw [LinearMap.mem_ker]
      have hpU : (p : V) ∈ U₁ := hN'U p.2
      show U₁.mkQ (p : V) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hpU
    have hC : Dsub E N' U ≤ (Dsub E N U).comap (Submodule.inclusion hN'N) := by
      intro p hp
      unfold Dsub at hp ⊢
      simp only [Submodule.mem_comap] at hp ⊢
      exact sup_le_sup (img_mono hN'N) (inf_le_inf_left _ hN'N) hp
    have hB : Dsub E N U ⊔ B₀ ≤ Dsub E N U ⊔ LinearMap.range (Submodule.inclusion hN'N) := by
      rw [hB₀]
      refine sup_le le_sup_left (sup_le ?_ ?_)
      · intro m hm
        obtain ⟨n, rfl⟩ := (mem_smulRange l m).mp hm
        have hfn : f (n : V) ∈ N := hNE f hfE n n.2
        have hdiff : f (n : V) - l • (n : V) ∈ N' := by
          apply hN'ge
          refine Submodule.mem_inf.mpr ⟨N.sub_mem hfn (N.smul_mem l n.2), ?_⟩
          have hnWU : (n : V) ∈ W x ⊔ U₁ := hNWU n.2
          obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hnWU
          have key : f (n : V) - l • (n : V) = f b - l • b := by
            rw [← hab, map_add, hfl a ha, smul_add]
            abel
          show f (n : V) - l • (n : V) ∈ U₁
          rw [key]
          refine U₁.sub_mem (hEU₁ f hfE hb) ?_
          rw [← algebraMap_smul (FractionRing O) l b]
          exact U₁.smul_mem _ hb
        have hA : (⟨f (n : V), hfn⟩ : N) ∈ Dsub E N U := by
          show f (n : V) ∈ img E N ⊔ (U.restrictScalars O ⊓ N)
          refine Submodule.mem_sup_left ?_
          unfold img
          exact Submodule.subset_span ⟨f, hfE, (n : V), n.2, rfl⟩
        have hR : (⟨f (n : V), hfn⟩ : N) - l • n ∈ LinearMap.range (Submodule.inclusion hN'N) :=
          ⟨⟨_, hdiff⟩, Subtype.ext rfl⟩
        rw [← sub_sub_cancel (⟨f (n : V), hfn⟩ : N) (l • n)]
        exact Submodule.sub_mem _ (Submodule.mem_sup_left hA) (Submodule.mem_sup_right hR)
      · intro m hm
        rw [LinearMap.mem_ker] at hm
        have hmU : (m : V) ∈ U₁ := by
          have h0 : U₁.mkQ (m : V) = 0 := hm
          rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
        have hmN' : (m : V) ∈ N' := hN'ge (Submodule.mem_inf.mpr ⟨m.2, hmU⟩)
        exact Submodule.mem_sup_right ⟨⟨(m : V), hmN'⟩, Subtype.ext rfl⟩
    have hsplit := split (Dsub E N U) (Dsub E N U ⊔ B₀) le_sup_left (Submodule.inclusion hN'N)
      (Dsub E N' U) hiB hC hB
    have hq := quot_mono (M := N) (le_sup_right : B₀ ≤ Dsub E N U ⊔ B₀)
    rw [Finset.sum_insert hxS]
    calc Module.length O (N ⧸ Dsub E N U)
        ≤ Module.length O (N ⧸ (Dsub E N U ⊔ B₀)) + Module.length O (N' ⧸ Dsub E N' U) := hsplit
      _ ≤ (finrank (FractionRing O) (W x) : ℕ∞) * addVal O l +
            ∑ y ∈ S, (finrank (FractionRing O) (W y) : ℕ∞) * w y :=
          add_le_add (hq.trans hstep) hih
      _ ≤ _ := by
          first
            | (gcongr; exact hlw)
            | gcongr
            | exact add_le_add_right (mul_le_mul_of_nonneg_left hlw (zero_le _)) _
end Formalism.NG.QuotientPowerLengths
