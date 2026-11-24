-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_ff_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:42:23.1057+00:00
-- url     : https://prove2.me/submissions/7fd5316a-2479-42c8-ada3-5b2e76e601e1

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Theorems.Thm_Formalism_UG_P_tjcosets_orbit_gl
import Theorems.Thm_Formalism_UG_P_tjcosets_stab_le_par
import Theorems.Thm_Formalism_UG_P_tjcosets_orbit_par

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
theorem _root_.solution [Fintype 𝔽] (n j : ℕ) (hj : j ≤ n) :
    (tjcosets_par (𝔽 := 𝔽) n j).index *
        ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ (n - j) - Fintype.card 𝔽 ^ (i : ℕ)) =
      ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ)) := by
  classical
  have hk : n - j ≤ Module.finrank 𝔽 (Fin n → 𝔽) := by rw [Module.finrank_fin_fun]; omega
  have hk' : n - j ≤ Module.finrank 𝔽 (Fin (n - j) → 𝔽) := by simp
  have cGL : (MulAction.orbit (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).ncard =
      ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ)) := by
    have h := card_linearIndependent (K := 𝔽) (V := Fin n → 𝔽) hk
    rw [Module.finrank_fin_fun] at h
    rw [tjcosets_orbit_gl, ← Nat.card_coe_set_eq]
    exact h
  have cP : (MulAction.orbit (tjcosets_par (𝔽 := 𝔽) n j) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).ncard =
      ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ (n - j) - Fintype.card 𝔽 ^ (i : ℕ)) := by
    have h := card_linearIndependent (K := 𝔽) (V := Fin (n - j) → 𝔽) hk'
    rw [Module.finrank_fin_fun] at h
    rw [tjcosets_orbit_par, ← Nat.card_coe_set_eq, Nat.card_congr (tjcosets_equiv (𝔽 := 𝔽) n j)]
    exact h
  have hstab : (MulAction.stabilizer (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).relIndex
      (tjcosets_par n j) =
      (MulAction.orbit (tjcosets_par (𝔽 := 𝔽) n j) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽)).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
  have hmul := Subgroup.relIndex_mul_index (tjcosets_stab_le_par (𝔽 := 𝔽) n j)
  rw [MulAction.index_stabilizer, cGL, hstab, cP] at hmul
  rw [mul_comm]
  exact hmul
end Formalism.UG.P
