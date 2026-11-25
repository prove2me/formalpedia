-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_parts_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:29:27.820911+00:00
-- url     : https://prove2.me/submissions/28d0f353-1e77-455a-aa42-006b64f9bcf6

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_norm_le_gN_Rn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_le_max_zero_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_le_div_of_lower_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_le_big
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_one_add_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_gV_slice
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
namespace Formalism.FourierDecayAlt.P.Ux6
theorem _root_.solution : CoordinateSizesFromComponents := by
  intro hSM hU1 hU2 hZh hDet k p s ρ σ d hd hs K hK hK0
  obtain ⟨κ0, hκ0, hκK⟩ : ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ x ∈ K, κ0 ≤ x := by
    rcases K.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn h continuousOn_id
      exact ⟨x0, hK0 hx0, fun x hx => hmin hx⟩
  obtain ⟨C1, hC1⟩ := hU1 k (p + s) ρ (by omega)
  obtain ⟨C2, hC2⟩ := hU2 p s σ d hd
  set D1 := max C1 0 with hD1
  set D2 := max C2 0 with hD2
  have hD1n : 0 ≤ D1 := le_max_right _ _
  have hD2n : 0 ≤ D2 := le_max_right _ _
  set m0 := min 1 κ0 with hm0def
  have hm0 : 0 < m0 := lt_min one_pos hκ0
  set ca := D1 / m0
  set cc := 1 + D2 * D1 ^ p
  set cd := 1 + D2 * D1 ^ (p + 1)
  set ce := D1 / m0 ^ 2
  set cf := D1 / κ0
  have hca : 0 ≤ ca := div_nonneg hD1n hm0.le
  have hcc : 0 ≤ cc := by positivity
  have hcd : 0 ≤ cd := by positivity
  have hce : 0 ≤ ce := by positivity
  have hcf : 0 ≤ cf := div_nonneg hD1n hκ0.le
  refine ⟨ca + (1 + ca) + cc + cd + ce + cf, ?_⟩
  intro ξ Z γ hγ hDK
  set Zj := ZjH σ d ξ.2 Z with hZjdef
  have hgdef : gaXi k ρ σ d ξ Z γ =
      (Rn k (p + s) ρ ξ.1.1)⁻¹ * mMap k (p + s) ρ Zj γ * Rn k (p + s) ρ ξ.1.2 := rfl
  set g := gaXi k ρ σ d ξ Z γ with hg
  have hDj : DjU k (p + s) ρ g = Zj.det := by rw [DjU, hgdef, hZh]
  have hdetK : ‖Zj.det‖ ∈ K := hDj ▸ hDK
  have hdet_ge : κ0 ≤ ‖Zj.det‖ := hκK _ hdetK
  have hdet0 : Zj.det ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet_ge; linarith
  have hZ0 : G.detM Z ≠ 0 := by
    intro h; apply hdet0; rw [hZjdef, hDet]; simp [h]
  obtain ⟨u1, u2, u3, u4, u5⟩ := hC1 ξ.1.1 ξ.1.2 Zj γ hdet0 hγ
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := hC2 ξ.2 Z
  rw [← hgdef] at u1 u2 u3 u4 u5
  have hgGV : g ∈ B.GV k (p + s + ρ) := by
    rw [hgdef]; exact gV_slice _ _ _ ((hSM k (p + s) ρ).1 Zj γ hdet0 hγ)
  have hg1 : 1 ≤ B.gN g := BetaSesquilinearity.gN_ge_one hgGV
  have hgp : ∀ e : ℕ, 1 ≤ B.gN g ^ e := fun e => one_le_pow₀ hg1
  have hgp0 : ∀ e : ℕ, 0 ≤ B.gN g ^ e := fun e => le_trans zero_le_one (hgp e)
  have hmin : m0 ≤ min 1 ‖Zj.det‖ := min_le_min le_rfl hdet_ge

  have b1 : B.gN (Rn k (p + s) ρ ξ.1.1) ≤ ca * B.gN g ^ (p + s) := le_div_of_lower_bound (hgp0 _) hm0 hmin u1
  have b2 : B.gN (Rn k (p + s) ρ ξ.1.2) ≤ ca * B.gN g ^ (p + s) := le_div_of_lower_bound (hgp0 _) hm0 hmin u2
  have b3 : 1 + ‖ξ.1.1‖ ≤ (1 + ca) * B.gN g ^ (p + s) :=
    one_add_le (hgp _) ((norm_le_gN_Rn _).trans b1)
  have b4 : 1 + ‖ξ.1.2‖ ≤ (1 + ca) * B.gN g ^ (p + s) :=
    one_add_le (hgp _) ((norm_le_gN_Rn _).trans b2)

  have hmx0 : 0 ≤ mx Zj := norm_nonneg _
  have hmx : mx Zj ≤ D1 * B.gN g := le_max_zero_mul (le_trans zero_le_one hg1) u3
  have hmxp : ∀ e : ℕ, mx Zj ^ e ≤ D1 ^ e * B.gN g ^ e := fun e => by
    rw [← mul_pow]; exact pow_le_pow_left₀ hmx0 hmx e
  have head : ∀ (X : ℝ) (e : ℕ), X ≤ C2 * mx Zj ^ e → 1 + X ≤ (1 + D2 * D1 ^ e) * B.gN g ^ e := by
    intro X e hX
    apply one_add_le (hgp e)
    calc X ≤ D2 * mx Zj ^ e := le_max_zero_mul (pow_nonneg hmx0 e) hX
      _ ≤ D2 * (D1 ^ e * B.gN g ^ e) := mul_le_mul_of_nonneg_left (hmxp e) hD2n
      _ = D2 * D1 ^ e * B.gN g ^ e := by ring
  have b5 := head _ _ v1
  have b6 := head _ _ v2
  have b7 := head _ _ v3
  have b8 := head _ _ v4
  have b9 := head _ _ v5

  have hmin2 : m0 ^ 2 ≤ min 1 ‖Zj.det‖ ^ 2 := pow_le_pow_left₀ hm0.le hmin 2
  have b10 : B.gN γ ≤ ce * B.gN g ^ (2 * (p + s) + 1) :=
    le_div_of_lower_bound (hgp0 _) (by positivity) hmin2 u5

  have b11 : mx (Matrix.of Z)⁻¹ ≤ cf * B.gN g ^ (p + s - 1) :=
    (v6 hZ0).trans (le_div_of_lower_bound (hgp0 _) hκ0 hdet_ge u4)
  set Ct := ca + (1 + ca) + cc + cd + ce + cf with hCt
  refine ⟨hg1, le_big (hgp0 _) (by linarith) b1, le_big (hgp0 _) (by linarith) b2,
    le_big (hgp0 _) (by linarith) b3, le_big (hgp0 _) (by linarith) b4,
    le_big (hgp0 _) (by linarith) b5, le_big (hgp0 _) (by linarith) b6,
    le_big (hgp0 _) (by linarith) b7, le_big (hgp0 _) (by linarith) b8,
    le_big (hgp0 _) (by linarith) b9, le_big (hgp0 _) (by linarith) b10,
    le_big (hgp0 _) (by linarith) b11⟩
end Formalism.FourierDecayAlt.P.Ux6
