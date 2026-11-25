-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.quotLocal_of_quotientLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:05:17.437802+00:00
-- url     : https://prove2.me/submissions/1255d051-6ecc-45aa-8236-ce9e2cb4fba5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_QuotLocalOfQuotientLength
import Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_coordK_injective
import Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_cK_coordK
import Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_inf_ker_eq_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open TieQL
namespace Formalism.L2.Pj.QAt
theorem _root_.solution (h : Formalism.LatticeBaseChangeAlt.QuotientLength) :
    ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.QuotLocalStatement := by
  intro O Q _ _ _ _ _ ρ hb c th hdet
  obtain ⟨b⟩ := hb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmat : (Matrix.of fun i j => cK b c (coordK b (th j)) i) =
      (Matrix.of fun i j => c i (th j)).map (algebraMap O (FractionRing O)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.map_apply, cK_coordK]
  have hdetK : algebraMap O (FractionRing O) (Matrix.of fun i j => c i (th j)).det =
      (Matrix.of fun i j => cK b c (coordK b (th j)) i).det * algebraMap O (FractionRing O) 1 := by
    rw [map_one, mul_one, hmat, RingHom.map_det]
    rfl
  obtain ⟨m, hm, hle⟩ := h O (FractionRing O) (Fin ρ → FractionRing O) ϖ hϖ ρ (cK b c)
    (LinearMap.ker (cK b c)) le_rfl (LinearMap.range (coordK b)) 0 0 (fun j => coordK b (th j))
    (by
      rintro x ⟨q, rfl⟩ i
      exact ⟨c i q, by simp [cK_coordK]⟩)
    (by intro j; simp)
    _ 1 hdet one_ne_zero hdetK
  let eQ : Q ≃ₗ[O] LinearMap.range (coordK b) := LinearEquiv.ofInjective (coordK b) (coordK_injective b)
  have hT : ((LinearMap.range (coordK b) ⊓ (LinearMap.ker (cK b c)).restrictScalars O) ⊔
      Submodule.span O (Set.range fun j => (algebraMap O (FractionRing O) ϖ) ^ (0 : ℕ) • coordK b (th j))).comap
        (LinearMap.range (coordK b)).subtype =
      (Submodule.span O (Set.range th)).map (eQ : Q →ₗ[O] LinearMap.range (coordK b)) := by
    rw [inf_ker_eq_bot b c th hdet, bot_sup_eq]
    simp only [pow_zero, one_smul]
    ext ⟨v, hv⟩
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp hv
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map]
    constructor
    · intro hq
      have h1 : coordK b q ∈ (Submodule.span O (Set.range th)).map (coordK b) := by
        rw [Submodule.map_span, ← Set.range_comp]
        exact hq
      obtain ⟨y, hy, hyq⟩ := h1
      refine ⟨y, hy, Subtype.ext ?_⟩
      rw [LinearEquiv.coe_coe, LinearEquiv.ofInjective_apply]
      exact hyq
    · rintro ⟨y, hy, hyq⟩
      have h2 : coordK b y = coordK b q := by
        have h3 := congrArg Subtype.val hyq
        rwa [LinearEquiv.coe_coe, LinearEquiv.ofInjective_apply] at h3
      rw [← h2]
      have h4 := Submodule.mem_map_of_mem (f := coordK b) hy
      rw [Submodule.map_span, ← Set.range_comp] at h4
      exact h4
  have e := Submodule.Quotient.equiv (Submodule.span O (Set.range th)) _ eQ hT.symm
  have hm' : m ≤ (IsDiscreteValuationRing.addVal O (Matrix.of fun i j => c i (th j)).det).toNat := by
    simp at hle
    exact_mod_cast hle
  calc Module.length O (Q ⧸ Submodule.span O (Set.range th)) = (m : ℕ∞) := e.length_eq.trans hm
    _ ≤ _ := (Nat.cast_le.mpr hm').trans (ENat.coe_toNat_le_self _)
end Formalism.L2.Pj.QAt
