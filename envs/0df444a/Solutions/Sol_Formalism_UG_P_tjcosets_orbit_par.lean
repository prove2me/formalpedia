-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_orbit_par
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:12.787796+00:00
-- url     : https://prove2.me/submissions/c486c254-b2fd-467e-98ae-3a4f7155610c

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Theorems.Thm_Formalism_UG_P_GL_smul_standard_tuple
import Theorems.Thm_Formalism_UG_P_tjcosets_mem_par
import Theorems.Thm_Formalism_UG_P_GL_columns_linearIndependent
import Theorems.Thm_Formalism_UG_P_tjcosets_exists_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {𝔽 : Type} [Field 𝔽]
namespace Formalism.UG.P
theorem _root_.solution [Finite 𝔽] (n j : ℕ) :
    MulAction.orbit (tjcosets_par (𝔽 := 𝔽) n j) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) =
      {w : TjcosetsFr (n - j) n 𝔽 | LinearIndependent 𝔽 (w : Fin (n - j) → Fin n → 𝔽) ∧
        ∀ i (a : Fin n), (a : ℕ) < j → w i a = 0} := by
  ext w
  simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp⟩
    have hp' : (p : GL (Fin n) 𝔽) • (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) = w := hp
    rw [GL_smul_standard_tuple] at hp'
    subst hp'
    refine ⟨GL_columns_linearIndependent n j (p : GL (Fin n) 𝔽), fun i a ha => ?_⟩
    have h0 := (tjcosets_mem_par n j (p : GL (Fin n) 𝔽)).1 p.2 a (tjcosets_idx n j i) ha
      (by simp [tjcosets_idx])
    simpa [Matrix.col] using h0
  · rintro ⟨hw, hz⟩
    obtain ⟨g, hg⟩ := tjcosets_exists_smul n j w hw
    have hg' := hg
    rw [GL_smul_standard_tuple] at hg'
    have hgP : g ∈ tjcosets_par n j := by
      rw [tjcosets_mem_par]
      intro a b ha hb
      have h1 : (g : Matrix (Fin n) (Fin n) 𝔽).col (tjcosets_idx n j ⟨b - j, by omega⟩) a
          = w ⟨b - j, by omega⟩ a := congrFun (congrFun hg' _) a
      rw [tjcosets_idx_sub n j b hb] at h1
      have h2 := h1.trans (hz _ a ha)
      simpa [Matrix.col] using h2
    refine ⟨⟨g, hgP⟩, ?_⟩
    rw [Subgroup.smul_def]
    exact hg
end Formalism.UG.P
