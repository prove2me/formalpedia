-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_pairD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:16.43387+00:00
-- url     : https://prove2.me/submissions/f2bd2736-9543-4288-ba1f-1b2b1e311bba

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_pairD_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_smul_cocompact
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integrable_inner_of_memLp
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_memLp_comp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_norm_of_mem_rootSet_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_one_mem_rootSet_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_inner_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_integral_psi_conv
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_integral_psi_moving


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt bt' : ℂ → H}
    (hb : MemLp (bz s bt) 2 volume) (hb' : MemLp (bz s bt') 2 volume) {α : Type} {l : Filter α}
    (x x' ρ : α → ℂ) (σ : ℂ) (hρ0 : ∀ᶠ a in l, ρ a ≠ 0) (hρ : Tendsto ρ l (𝓝 1))
    (hsh : Tendsto (fun a => (s : ℂ) * (ρ a * x' a - x a)) l (𝓝 σ))
    (hne : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 1 → Tendsto (fun a => ζ * ρ a * x' a - x a) l (cocompact ℂ)) :
    Tendsto (fun a => pairD s β ε bt bt' (x a) (x' a) (ρ a)) l
      (𝓝 (∫ z, G.psi β (σ * z) • ⟪bz s bt z, bz s bt' z⟫_ℂ)) := by
  set L : ℂ := ∫ z, G.psi β (σ * z) • ⟪bz s bt z, bz s bt' z⟫_ℂ with hL
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hlim : ∀ ζ ∈ G.rootSet s 1, Tendsto (fun a => ∫ z, termZ s β bt bt' (x a) (x' a) (ρ a) ζ z) l
      (𝓝 (if ζ = 1 then L else 0)) := by
    intro ζ hζ
    have hζn := norm_of_mem_rootSet_one hs hζ
    have hζ0 : ζ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hζn; exact zero_ne_one hζn
    have hf0 : Integrable (fun z => ⟪bz s bt z, bz s bt' (ζ * z)⟫_ℂ) :=
      integrable_inner_of_memLp hb (memLp_comp_mul hb' ζ hζ0)
    have hfi : ∀ᶠ a in l, Integrable (fun z => ⟪bz s bt z, ((‖ρ a‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ a * z)⟫_ℂ) := by
      filter_upwards [hρ0] with a ha
      exact integrable_inner_of_memLp hb ((memLp_comp_mul hb' (ζ * ρ a) (mul_ne_zero hζ0 ha)).const_smul _)
    have hL1 : Tendsto (fun a => ∫ z, ‖⟪bz s bt z, ((‖ρ a‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ a * z)⟫_ℂ -
        ⟪bz s bt z, bz s bt' (ζ * z)⟫_ℂ‖) l (𝓝 0) := by
      have hζρ : Tendsto (fun a => ζ * ρ a) l (𝓝 ζ) := by
        simpa using (tendsto_const_nhds (x := ζ)).mul hρ
      have h1 := (tendsto_inner_dil (bz s bt) (bz s bt') hb hb' ζ hζ0).comp hζρ
      refine h1.congr fun a => ?_
      simp only [Function.comp_apply, norm_mul, hζn, one_mul, Complex.ofReal_one, one_smul]
    by_cases h1 : ζ = 1
    · subst h1
      rw [if_pos rfl]
      have hw : Tendsto (fun a => (s : ℂ) * (1 * ρ a * x' a - x a)) l (𝓝 σ) := by simpa using hsh
      have := tendsto_integral_psi_conv β _ _ hf0 hfi hL1 _ σ hw
      simpa [termZ, hL] using this
    · rw [if_neg h1]
      have hw := tendsto_smul_cocompact (s : ℂ) hs0 _ (hne ζ hζ h1)
      have := tendsto_integral_psi_moving β hβ _ _ hf0 hfi hL1 _ hw
      simpa [termZ, mul_assoc] using this
  have hsum := tendsto_finsetSum (G.rootSet s 1) hlim
  rw [Finset.sum_ite_eq' (G.rootSet s 1) 1 (fun _ => L), if_pos (one_mem_rootSet_one hs)] at hsum
  refine hsum.congr' ?_
  filter_upwards [hρ0] with a ha
  exact (pairD_eq hs β hε hb hb' (x a) (x' a) (ρ a) ha).symm
end Formalism.FourierDecayAlt.P.PBK
