-- Prove2me | solution 3 for CritWinSpin.theorem_7_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:32:11.950644+00:00
-- url     : https://prove2.me/submissions/d90ca3ae-e893-4d6c-b74f-130c9fed8247
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Theorems.Thm_CritWinSpin_p7b_thm72_forge_to_error_wrapped
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

open CritWinSpin

theorem solution (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (F : BilinearFamily) (src : BinarySource F) (C : ℝ) (hC : 0 < C) (hsrc : SourceProps F src C)
    (w ε : ℝ) (Ac Cc : ℕ) (hw : 1 ≤ w) (hε : 0 < ε) (hεd : ε < dExp p)
    (hpar : GadgetParams p w ε Ac Cc)
    (Ccap : ℝ) (hCcap : 0 < Ccap)
    (liftF : Str → Str) (hliftF : CookPvsNP.PolyTimeComputable liftF) (slotM : PPT)
    (û : (d : ℕ) → (desc : Str) → WatersKey F desc d → ℚ) (d₁ : ℕ)
    (hlift : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      IsUhat S ((thetaQ p Ac Cc (src.n d) : ℚ) : ℝ) (cloudSize p Cc (src.n d)) (û d desc key) ∧
      liftF (encInst (src.ham d desc key)) =
        tupleCode [encInst (liftInst S p Ac Cc (src.ham d desc key) (û d desc key)),
          encRat (û d desc key)])
    (hdec : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      LhatDecodes (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key)))
    (k T : ℕ → ℕ) (hk : EffPoly k) (hk₁ : ∀ d, 1 ≤ k d) (hT : EffPoly T)
    (hTk : ∀ d, ⌈Ccap * ((k d : ℝ) + 1 + (src.n d : ℝ) ^ 2)⌉₊ ≤ T d)
    (v₁ v₂ : ℕ → ℝ)
    (hv₁ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
          (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (k d))
        (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
          (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (k d)) ≤ v₁ d)
    (hv₂ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
          (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (k d + 1))
        (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
          (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (k d + 1)) ≤ v₂ d)
    (A : PPT) :
    (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
      1 - C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errExt S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) ∧
    (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
      1 - C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errAmp S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) := by
  have hsrc' := hsrc
  rcases hsrc with ⟨_hwidth, _hham, _hpsi, _hprops, hforge⟩
  have hTpos : ∀ d, 1 ≤ T d := by
    intro d
    have harg : 0 < Ccap * ((k d : ℝ) + 1 + (src.n d : ℝ) ^ 2) := by positivity
    have hc : 0 < ⌈Ccap * ((k d : ℝ) + 1 + (src.n d : ℝ) ^ 2)⌉₊ :=
      Nat.ceil_pos.mpr harg
    exact le_trans hc (hTk d)
  rcases p7b_thm72_forge_to_error_wrapped
      S p hS hp F src C hC hsrc' w ε Ac Cc hw hε hεd hpar
      Ccap hCcap liftF hliftF slotM û d₁ hlift hdec
      k T hk hk₁ hT hTk v₁ v₂ hv₁ hv₂ A with ⟨⟨Fext, d₀E, hE⟩, ⟨Famp, d₀A, hA⟩⟩
  rcases hforge Fext T hT hTpos with ⟨Bext, d₀BE, hBE⟩
  rcases hforge Famp T hT hTpos with ⟨Bamp, d₀BA, hBA⟩
  constructor
  · refine ⟨Bext, max d₀BE d₀E, ?_⟩
    intro d hd
    have hb := hBE d (le_trans (le_max_left _ _) hd)
    have he := hE d (le_trans (le_max_right _ _) hd)
    linarith
  · refine ⟨Bamp, max d₀BA d₀A, ?_⟩
    intro d hd
    have hb := hBA d (le_trans (le_max_left _ _) hd)
    have ha := hA d (le_trans (le_max_right _ _) hd)
    linarith
