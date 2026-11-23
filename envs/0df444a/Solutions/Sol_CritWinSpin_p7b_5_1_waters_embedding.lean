-- Prove2me | solution 1 for CritWinSpin.p7b_5_1_waters_embedding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:54:53.491569+00:00
-- url     : https://prove2.me/submissions/7aa54c22-5bf1-4578-8986-ef460f2ae373
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CritWinSpin_SourceReduction
import Theorems.Thm_CritWinSpin_p7b_5_1_waters_compiler
import Theorems.Thm_CritWinSpin_p7b_5_1_waters_security
import Theorems.Thm_CritWinSpin_p7b_5_1_zero_field_maps
import Theorems.Thm_CritWinSpin_p7b_5_1_zero_field_wrapper
import Theorems.Thm_CritWinSpin_p7b_5_1_zerofield_math

open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp CritWinSpin
open scoped BigOperators
set_option autoImplicit false

theorem solution
    (hP : ∀ (F : BilinearFamily), ∀ d : ℕ, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → (F.q desc).Prime) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : BilinearFamily, ∃ circ : WatersCircuit F,
      PolyBounded circ.n0 ∧ (∀ d, d ^ 2 ≤ circ.n0 d) ∧
      (∃ evalF : Str → Str, CookPvsNP.PolyTimeComputable evalF ∧
        ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
          (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
          evalF (tupleCode [pkCode F d desc key, List.ofFn m, F.encG desc s₁, F.encG desc s₂]) =
            List.ofFn (circ.evalCfg d desc key m s₁ s₂)) ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
        circ.psi d desc key (circ.evalCfg d desc key m s₁ s₂) = m) ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (m₁ m₂ : Fin d → Bool) (r₁ r₂ : Fin (F.q desc)),
        circ.evalCfg d desc key m₁ (expo r₁) (signS2 key m₁ (expo r₁)) =
          circ.evalCfg d desc key m₂ (expo r₂) (signS2 key m₂ (expo r₂)) →
        m₁ = m₂ ∧ r₁ = r₂) ∧
      SourceProps F circ.toSource C ∧
      (∃ hamF_hat : Str → Str, CookPvsNP.PolyTimeComputable hamF_hat ∧
        ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
          hamF_hat (pkCode F d desc key) = encInst ((hatSource circ.toSource).ham d desc key)) ∧
      (∃ psiF_hat : Str → Str, CookPvsNP.PolyTimeComputable psiF_hat ∧
        ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
          (y : BinCfg (circ.n0 d + 1)),
          psiF_hat (tupleCode [pkCode F d desc key, List.ofFn y]) =
            List.ofFn ((hatSource circ.toSource).psi d desc key y)) ∧
      (∀ (A : PPT) (T : ℕ → ℕ), EffPoly T → (∀ d, 1 ≤ T d) →
        ∃ B_wrap : PPT, ∀ (d : ℕ) (desc : Str) (key : WatersKey F desc d)
          (Fs : Fin (T d) → BinCfg (circ.n0 d)),
          (1 / (2 : ℝ) ^ (T d)) * ∑ ts : Fin (T d) → Bool,
            A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
                List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
              (fun s => ∃ y_hat : BinCfg (circ.n0 d + 1), s = List.ofFn y_hat ∧
                hatProd y_hat ∈ circ.omega d desc key ∧
                ∀ t, circ.psi d desc key (hatProd y_hat) ≠ circ.psi d desc key (Fs t)) ≤
          B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
            (fun s => ∃ y : BinCfg (circ.n0 d), s = List.ofFn y ∧ y ∈ circ.omega d desc key ∧
              ∀ t, circ.psi d desc key y ≠ circ.psi d desc key (Fs t))) := by
  obtain ⟨_, _, _, _, hgenLaw_eq⟩ := p7b_5_1_zerofield_math
  obtain ⟨C, hC_pos, hCDH⟩ := p7b_5_1_waters_security
  refine ⟨C, hC_pos, fun F => ?_⟩
  obtain ⟨circ, hrecords, hgeometry, heff, hstat⟩ := p7b_5_1_waters_compiler F
  obtain ⟨hn0_poly, hn0_sq, heval, hpsi, hrecover, hinj⟩ := hrecords
  have hgen : ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc →
      ∀ (key : WatersKey F desc d) (y : BinCfg (circ.n0 d)),
        circ.genLaw d desc key y = unifOn (circ.omega d desc key) y := by
    intro d hd desc hdesc key y
    exact hgenLaw_eq F circ d desc key (hP F d hd desc hdesc)
      (hinj d hd desc hdesc key) y
  have hsecurity : SourceSecurity F circ.toSource C :=
    hCDH F circ ⟨hn0_poly, hn0_sq, heval, hpsi, hrecover, hinj⟩ hgen
  have hsrc : SourceProps F circ.toSource C :=
    ⟨hgeometry, heff.1, heff.2, hstat, hsecurity⟩
  obtain ⟨hham_hat, hpsi_hat⟩ := p7b_5_1_zero_field_maps F circ.toSource heff
  have hwrap : ∀ (A : PPT) (T : ℕ → ℕ), EffPoly T → (∀ d, 1 ≤ T d) →
      ∃ B_wrap : PPT, ∀ (d : ℕ) (desc : Str) (key : WatersKey F desc d)
        (Fs : Fin (T d) → BinCfg (circ.n0 d)),
        (1 / (2 : ℝ) ^ (T d)) * ∑ ts : Fin (T d) → Bool,
          A.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t =>
              List.ofFn (Fin.cons (ts t) (fun i => ts t == Fs t i))))
            (fun s => ∃ y_hat : BinCfg (circ.n0 d + 1), s = List.ofFn y_hat ∧
              hatProd y_hat ∈ circ.omega d desc key ∧
              ∀ t, circ.psi d desc key (hatProd y_hat) ≠ circ.psi d desc key (Fs t)) ≤
        B_wrap.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
          (fun s => ∃ y : BinCfg (circ.n0 d), s = List.ofFn y ∧ y ∈ circ.omega d desc key ∧
            ∀ t, circ.psi d desc key y ≠ circ.psi d desc key (Fs t)) := by
    intro A T hT hTpos
    exact p7b_5_1_zero_field_wrapper F circ.toSource A T hT hTpos
  exact ⟨circ, hn0_poly, hn0_sq, heval, hpsi, hinj, hsrc, hham_hat, hpsi_hat, hwrap⟩
