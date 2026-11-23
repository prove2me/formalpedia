-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.norm_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:41.599978+00:00
-- url     : https://prove2.me/submissions/36d31512-60b2-43da-9538-3615ac23b449

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_two_le_q

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]
variable [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ} (hs : ∀ x : K, star x = x ^ q) (hc : Fintype.card K = q ^ 2)
    (t : K) (ht : t ≠ 0) (hst : star t = t) : ∃ l : K, star l * l = t := by
  classical
  have hq := two_le_q hc
  have hcardU : Nat.card Kˣ = (q - 1) * (q + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hc]
    obtain ⟨s, rfl⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (s + 1) ^ 2 = s * (s + 1 + 1) + 1 := by ring
    omega
  have h1 : Nat.card (powMonoidHom (q + 1) : Kˣ →* Kˣ).range = q - 1 := by
    rw [IsCyclic.card_powMonoidHom_range, hcardU, Nat.gcd_eq_right (Dvd.intro_left _ rfl),
      Nat.mul_div_cancel _ (by omega)]
  have h2 : Nat.card (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker = q - 1 := by
    rw [IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_eq_right (Dvd.intro _ rfl)]
  have hle : (powMonoidHom (q + 1) : Kˣ →* Kˣ).range ≤ (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply]
    rw [← pow_mul, mul_comm, ← hcardU]
    exact pow_card_eq_one'
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h1, h2])
  have hmem : Units.mk0 t ht ∈ (powMonoidHom (q - 1) : Kˣ →* Kˣ).ker := by
    rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply]
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [hs] at hst
    have : t ^ (q - 1) * t = 1 * t := by
      rw [← pow_succ, one_mul, Nat.sub_add_cancel (by omega)]; exact hst
    exact mul_right_cancel₀ ht this
  rw [← heq] at hmem
  obtain ⟨x, hx⟩ := hmem
  refine ⟨(x : K), ?_⟩
  rw [hs, ← pow_succ]
  have := congrArg Units.val hx
  simpa using this
end Formalism.FourierDecayAlt.P.S3x5
