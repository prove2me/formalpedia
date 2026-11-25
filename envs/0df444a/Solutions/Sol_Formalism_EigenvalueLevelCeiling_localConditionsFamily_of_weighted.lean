-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.localConditionsFamily_of_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:34:53.399193+00:00
-- url     : https://prove2.me/submissions/487308a3-bc8d-41ff-af0c-b4e11b3948a9

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (h : LocalConditionsWeighted)
    (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K) (hMk : IsMackey U ψ)
    (V₀ : Submodule K Z) (e : Z →ₗ[K] Z) (he : e ∘ₗ e = e) (hr : LinearMap.range e = V₀)
    (M Th ThK Th0 ThJ X₃ X₄ : Submodule (𝓞 K) Z)
    (hM : IsLatIn ⊤ M) (hTh : IsLatIn ⊤ Th) (hThK : IsLatIn ⊤ ThK) (hle : Th ≤ M) (hFG : Th0.FG)
    (hEig : Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K))
    (hMs : ∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M)
    (hTs : ∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th)
    (σ : K) (hσ : σ ≠ 0) (hsc : Th ≤ sc σ ThK)
    (hdata : sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0)
    (a : K) (E : ℕ) (r : ℝ) (ha : a ≠ 0) (hE : vw w a = (E : ℤ))
    (hT0 : ∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r)
    (h0 : IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))))
    (hJ : IsLatIn (eig ρ U ψ ⊓ V₀) (ThJ.map (e.restrictScalars (𝓞 K)))) (h0J : Th0 ≤ ThJ)
    (h3 : IsLatIn (eig ρ U ψ ⊓ V₀) X₃) (h4 : IsLatIn (eig ρ U ψ ⊓ V₀) X₄) (h34 : X₃ ≤ X₄)
    (ε : ℝ)
    (hTW : (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε)
    (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z) (hinj : Function.Injective φ)
    (hrng : LinearMap.range φ = eig ρ U ψ ⊓ V₀)
    (Mj Tj : Submodule (𝓞 K) (Fin d → K))
    (hMj : Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M)
    (hTj : Tj.map (φ.restrictScalars (𝓞 K)) = X₄) :
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε := by
  have hfix : X₄.map (e.restrictScalars (𝓞 K)) = X₄ := by
    have h4c := h4
    obtain ⟨-, h4s⟩ := h4c
    have hsub : ∀ x ∈ X₄, e x = x := by
      intro x hx
      have hx1 : x ∈ Submodule.span K (X₄ : Set Z) := Submodule.subset_span hx
      rw [h4s] at hx1
      have hx2 : x ∈ LinearMap.range e := by
        rw [hr]
        exact (Submodule.mem_inf.1 hx1).2
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx2
      rw [← LinearMap.comp_apply e e, he]
    ext x
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hsub y hy]
      exact hy
    · intro hx
      exact ⟨x, hx, hsub x hx⟩
  have hid : X₄.map ((LinearMap.id : Z →ₗ[K] Z).restrictScalars (𝓞 K)) = X₄ := by
    ext x
    simp
  exact h K Z w P ρ U ψ hMk V₀ e he hr M Th Th ThK Th0 ThJ X₃ hM hTh hTh hThK le_rfl hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 Z LinearMap.id e LinearMap.id X₄
    (by rw [LinearMap.id_comp, LinearMap.comp_id]) (fun x _ => by simp)
    (by rw [hid, hfix]; exact h4) (by rw [hid, hfix]; exact h34) ε hTW d φ hinj hrng Mj Tj hMj
    (by rw [hTj, hfix, hid, hid])
end Formalism.EigenvalueLevelCeiling
