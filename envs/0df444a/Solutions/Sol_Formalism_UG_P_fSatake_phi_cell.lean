-- Prove2me | solution 1 for Formalism.UG.P.fSatake_phi_cell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:15.901407+00:00
-- url     : https://prove2.me/submissions/96e94b94-f2bc-4ea6-904a-7359765ba1ec

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
import Theorems.Thm_Formalism_UG_P_fSatake_borel_tMat
import Theorems.Thm_Formalism_UG_P_fSatake_tMat_exists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG
noncomputable section
namespace Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
private lemma isBorelU_mul {b c : GU σ n} (hb : IsBorelU b) (hc : IsBorelU c) :
    IsBorelU (b * c) := by
  have hB : Matrix.BlockTriangular ⟪b⟫ id := fun i j h => hb i j h
  have hC : Matrix.BlockTriangular ⟪c⟫ id := fun i j h => hc i j h
  intro i j hij
  show (⟪b⟫ * ⟪c⟫) i j = 0
  exact (hB.mul hC) hij
private lemma ordL_zpow_uniformizer {ϖ : L} (hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ))) (a : ℤ) :
    ordL (ϖ ^ a) = a := by
  have hv : Valued.v (ϖ ^ a) = ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul]
    simp
  have hne : Valued.v (ϖ ^ a) ≠ 0 := by
    rw [hv]
    exact WithZero.coe_ne_zero
  rw [ordL, dif_neg hne]
  have h2 : WithZero.unzero hne = Multiplicative.ofAdd (-a) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv]
  rw [h2, toAdd_ofAdd, neg_neg]
end Formalism.UG.P
end
end

set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
namespace Formalism.UG.P
theorem _root_.solution {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    {α : Fin m → ℂ} {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) {x u k : GU σ n}
    {a : Fin m → ℤ} (hu : IsUnipU u) (hk : k ∈ KU σ n)
    (hx : ⟪x⟫ = tMat ϖ n m a * ⟪u⟫ * ⟪k⟫) :
    φ x = (∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      φ 1 := by
  obtain ⟨huB, hu1⟩ := hu
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  have htB : IsBorelU t := fSatake_borel_tMat ht
  have hxe : x = t * u * k := by
    apply Subtype.ext
    apply Units.ext
    show ⟪x⟫ = ⟪t⟫ * ⟪u⟫ * ⟪k⟫
    rw [hx, ht]
  have h1 := hφ (t * u) 1 k (isBorelU_mul htB huB) hk
  rw [mul_one] at h1
  rw [hxe, h1]
  congr 1
  rw [chiDeltaU]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hi : (i : ℕ) < n := lt_of_lt_of_le i.isLt (by omega)
  have hd : ⟪t * u⟫ ⟨i, hi⟩ ⟨i, hi⟩ = ϖ ^ (a i) := by
    show (⟪t⟫ * ⟪u⟫) ⟨i, hi⟩ ⟨i, hi⟩ = _
    rw [ht, tMat, Matrix.diagonal_mul, hu1, mul_one]
    simp [i.isLt]
  rw [dif_pos hi, hd, ordL_zpow_uniformizer hϖ]
end Formalism.UG.P
