-- Prove2me | solution 1 for Formalism.UG.P.fSatake_hAct_sph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:12.577608+00:00
-- url     : https://prove2.me/submissions/cb042920-cf8b-48ae-a575-3cbc2e2ab119

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatake
import Theorems.Thm_Formalism_UG_P_fSatake_chiDelta_one
import Theorems.Thm_Formalism_UG_P_out_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution {q m : ℕ} {α : Fin m → ℂ} {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n))
    {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) : IsSphericalU q α (hAct (KU σ n) h φ) := by
  intro b g k hb hk
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hr : ∀ (y κ : GU σ n), κ ∈ KU σ n → φ (y * κ) = φ y := fun y κ hκ => by
    have := hφ 1 y κ hb1 hκ
    simpa [fSatake_chiDelta_one] using this
  have hl : ∀ y : GU σ n, φ (b * y) = chiDeltaU q α b * φ y := fun y => by
    have := hφ b y 1 hb (KU σ n).one_mem
    simpa using this
  obtain ⟨hbi, -⟩ := hh
  unfold hAct
  calc ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (b * g * k * x.out)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, chiDeltaU q α b * (h x.out • φ (g * (k * x.out))) := by
        refine finsum_congr fun x => ?_
        rw [show b * g * k * x.out = b * (g * (k * x.out)) by group, hl, smul_eq_mul, smul_eq_mul]
        ring
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * (k * x.out)) :=
        (mul_finsum _ _).symm
    _ = chiDeltaU q α b * ∑ᶠ x : GU σ n ⧸ KU σ n, h x.out • φ (g * x.out) := by
        congr 1
        symm
        rw [← finsum_comp_equiv (MulAction.toPerm k : (GU σ n ⧸ KU σ n) ≃ (GU σ n ⧸ KU σ n))]
        refine finsum_congr fun x => ?_
        obtain ⟨κ, hκ⟩ := out_smul (KU σ n) k x
        simp only [MulAction.toPerm_apply]
        rw [hκ]
        have e1 : h (k * x.out * κ) = h x.out := hbi ⟨k, hk⟩ κ x.out
        rw [e1, show g * (k * x.out * κ) = g * (k * x.out) * κ by group, hr _ _ κ.2]
end Formalism.UG.P
