-- Prove2me | solution 1 for CompanionTheory.Split.pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:05:03.760053+00:00
-- url     : https://prove2.me/submissions/f513ea97-3fb3-4378-ad8c-bffb05ee10c7

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SplitSep_exists_sep
import Theorems.Thm_GlobalTheory_mem_ALint_of_supported_at_split
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct Formalism.UG Formalism.L2
noncomputable section
open CompanionTheory CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
variable (s : SplitPlace L)
namespace CompanionTheory.Split
theorem _root_.solution {p : ℕ} (hp : s.Above p) {z : AL L} (hz : ∀ w, w ≠ s.v → compAt L w z = 0) :
    ∃ a : ℕ, ((p ^ a : ℕ) : AL L) * z ∈ ALint L := by
  have hv : Valued.v (p : s.v.adicCompletion L⁺) < 1 := by
    have := (s.split_mem_ideal _).1 ((s.split_alg_mem p).2 hp)
    rwa [map_natCast, show (((p : 𝓞 L) : 𝓞 L) : L) = p from map_natCast (algebraMap (𝓞 L) L) p, map_natCast] at this
  have key : ∀ y : s.v.adicCompletion L⁺, ∃ a : ℕ, ∀ b, a ≤ b → Valued.v ((p : s.v.adicCompletion L⁺) ^ b * y) ≤ 1 := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, fun _ _ => by simp⟩
    have hy' : Valued.v y ≠ 0 := (map_ne_zero _).2 hy
    obtain ⟨a, ha⟩ := exists_pow_lt₀ hv (Units.mk0 _ (inv_ne_zero hy'))
    refine ⟨a, fun b hb => ?_⟩
    rw [map_mul, map_pow, ← le_mul_inv_iff₀ (zero_lt_iff.2 hy'), one_mul]
    exact (pow_le_pow_right_of_le_one' hv.le hb).trans ha.le
  obtain ⟨a, ha⟩ := key (s.proj z)
  obtain ⟨b, hb⟩ := key (s.proj (conjAL L z))
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  refine ⟨a + b, GlobalTheory.mem_ALint_of_supported_at_split L s e he he' _ (fun w hw => by rw [map_mul, hz w hw, mul_zero]) ?_ ?_⟩
  · rw [map_mul, map_natCast, Nat.cast_pow]
    exact ha _ (Nat.le_add_right _ _)
  · rw [map_mul, map_mul, map_natCast, map_natCast, Nat.cast_pow]
    exact hb _ (Nat.le_add_left _ _)
end CompanionTheory.Split
