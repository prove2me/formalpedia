-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.ch_inert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:36:42.270508+00:00
-- url     : https://prove2.me/submissions/becfaf09-943c-470b-b06c-349e57772b2b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_one_div_eq_gam_add_rho
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_frobSum_alt
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
    {d : ℕ} (hd : Even d) (l : ℕ) (hl : l.Prime) (hlodd : Odd l)
    (r n j j' rh h : ℕ) (hr : r = n + j + j') (hh : h + rh = r) (hrh : rh ≤ j')
    (big : ZMod d → Prop) (halt : ∀ b, big (b + 1) ↔ ¬ big b) (p : ZMod d → ℕ)
    (hpb : ∀ b, big b → p b = n + j) (hps : ∀ b, ¬ big b → p b = j')
    (a : ZMod d) (ha : big a) (α : Matrix (Fin (p a)) (Fin h) R)
    (S : Matrix (Fin n) (Fin (p a)) R) (W : Matrix (Fin (p a)) (Fin n) R) (hSW : S * W = 1)
    (l1 l2 : ZMod d → ℝ) (hDET : CorDET l p l1 l2 a) (hAi : ThmAi l r rh p l2 a)
    (hAiii : ThmAiii v α (l1 a)) :
    (lenCoker v α ≤ (xInert l r j' rh : WithTop ℝ) ∧
      xInert l r j' rh = ((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l ∧
      xInert l r j' rh ≤ (n : ℝ) * gam l + ((j : ℝ) + j') / ((l : ℝ) - 1)) ∧
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
              (((y : ℝ) * xInert l r j' rh : ℝ) : WithTop ℝ) := by
  subst hr
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hu := one_div_eq_gam_add_rho hl.one_lt
  have hg0 : 0 ≤ gam l := by
    unfold gam
    exact div_nonneg (by positivity) (by nlinarith)
  have hr0 : 0 ≤ rho l := by
    unfold rho
    exact div_nonneg zero_le_one (by nlinarith)
  have hpa : p a = n + j := hpb a ha
  have hfs := frobSum_alt hl.one_lt n j j' big halt p hpb hps a ha
  have hrhR : (rh : ℝ) ≤ j' := by exact_mod_cast hrh
  have hD : l1 a - l2 a = (p a : ℝ) / ((l : ℝ) - 1) - frobSum l p a := hDET
  have hA : l2 a ≤ ((n + j + j' : ℕ) - (rh : ℝ) - p a) / ((l : ℝ) - 1) := hAi
  rw [hpa, hfs, div_eq_mul_one_div, hu] at hD
  rw [hpa, div_eq_mul_one_div, hu] at hA
  push_cast at hD hA
  have hxi : xInert l (n + j + j') j' rh = (((n + j + j' : ℕ) : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l := by
    unfold xInert
    rw [div_eq_mul_one_div, hu]
    push_cast
    ring
  have hlen : lenCoker v α ≤ (xInert l (n + j + j') j' rh : WithTop ℝ) := by
    have h3 : lenCoker v α = (l1 a : WithTop ℝ) := hAiii
    rw [h3]
    refine WithTop.coe_le_coe.mpr ?_
    rw [hxi]
    push_cast
    nlinarith
  refine ⟨⟨hlen, hxi, ?_⟩, ch_minor v hv S W hSW α _ hlen⟩
  rw [hxi, div_eq_mul_one_div, hu]
  push_cast
  have e1 := mul_nonneg (Nat.cast_nonneg (α := ℝ) rh) hg0
  have e2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) j') hg0
  have e3 := mul_nonneg (Nat.cast_nonneg (α := ℝ) j) hr0
  have e4 := mul_nonneg (Nat.cast_nonneg (α := ℝ) rh) hr0
  nlinarith
end Formalism.L2.FormalSeriesBounds.S4
