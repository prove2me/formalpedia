-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.ch_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:36:43.794902+00:00
-- url     : https://prove2.me/submissions/1db25373-be9f-4eff-9771-d552b445666a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_frobSum_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_ch_minor

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x)
    {d : ℕ} (hd : d ≠ 0) (l : ℕ) (hl : l.Prime) (hlodd : Odd l)
    (r n j j' rh h P : ℕ) (hP : P + j' = r) (hh : h + rh = r) (hrh : rh ≤ j')
    (p : ZMod d → ℕ) (hp : ∀ τ, p τ = P)
    (a : ZMod d) (α : Matrix (Fin (p a)) (Fin h) R)
    (S : Matrix (Fin n) (Fin (p a)) R) (W : Matrix (Fin (p a)) (Fin n) R) (hSW : S * W = 1)
    (l1 l2 : ZMod d → ℝ) (hDET : CorDET l p l1 l2 a) (hAi : ThmAi l r rh p l2 a)
    (hAiii : ThmAiii v α (l1 a)) :
    (lenCoker v α ≤ ((((j' : ℝ) - rh) / ((l : ℝ) - 1) : ℝ) : WithTop ℝ) ∧
      ((j' : ℝ) - rh) / ((l : ℝ) - 1) ≤ ((j : ℝ) + j') / ((l : ℝ) - 1)) ∧
    ∃ f : Fin n → Fin h, StrictMono f ∧
      v (Matrix.of fun k c => (S * α) c (f k)).det ≤ lenCoker v α ∧
      ∀ (F : Type) [CommRing F] [Algebra R F] (D : Fin n → Fin n → Derivation R F F)
        (χ : Fin n → F) (ev : F →ₐ[R] R),
        (∀ ρ c σ, D ρ c (χ σ) = (if σ = ρ then (S * α) c (f ρ) else 0) • χ σ) →
        (∀ σ, ev (χ σ) = 1) →
        ∀ y : ℕ,
          ev (((detOp fun ρ c => (D ρ c : F →ₗ[R] F)) ^ y) (∏ σ, χ σ)) =
              (Matrix.of fun k c => (S * α) c (f k)).det ^ y ∧
            v ((Matrix.of fun k c => (S * α) c (f k)).det ^ y) ≤
              (((y : ℝ) * (((j' : ℝ) - rh) / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hfs := frobSum_const hl.one_lt P p hp a
  have hD : l1 a - l2 a = (p a : ℝ) / ((l : ℝ) - 1) - frobSum l p a := hDET
  have hA : l2 a ≤ ((r : ℝ) - rh - p a) / ((l : ℝ) - 1) := hAi
  rw [hp, hfs, sub_self] at hD
  rw [hp] at hA
  have hPR : (P : ℝ) + j' = r := by exact_mod_cast hP
  have hb : l1 a ≤ ((j' : ℝ) - rh) / ((l : ℝ) - 1) := by
    have : (r : ℝ) - rh - P = (j' : ℝ) - rh := by linarith
    rw [this] at hA
    linarith
  have hlen : lenCoker v α ≤ ((((j' : ℝ) - rh) / ((l : ℝ) - 1) : ℝ) : WithTop ℝ) := by
    have h3 : lenCoker v α = (l1 a : WithTop ℝ) := hAiii
    rw [h3]
    exact WithTop.coe_le_coe.mpr hb
  refine ⟨⟨hlen, ?_⟩, ch_minor v hv S W hSW α _ hlen⟩
  apply div_le_div_of_nonneg_right _ hl0.le
  have : (0 : ℝ) ≤ rh := Nat.cast_nonneg rh
  have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith
end Formalism.L2.FormalSeriesBounds.S4
