-- Prove2me | solution 2 for CritWinSpin.theorem_5_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Maxliu
-- created : 2026-11-17T11:42:13.477919+00:00
-- url     : https://prove2.me/submissions/ce91afa4-7097-42aa-a599-aac46d0f4816
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CritWinSpin_BinarySource
import Theorems.Thm_CritWinSpin_p7b_theorem_5_1_from_waters_prime
import Theorems.Thm_CritWinSpin_p7b_waters_prime
open QAlgorithms.Complexity QuantumPRC
set_option autoImplicit false

open CritWinSpin

/-- Theorem 5.1 (p.19, eqs. (26)–(27)) reduced to a bridge lemma plus its prerequisite. -/
theorem solution  :
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
        (y : BinCfg (circ.n0 d)), circ.genLaw d desc key y = unifOn (circ.omega d desc key) y) ∧
      SourceProps F circ.toSource C ∧
      SourceProps F (hatSource circ.toSource) C ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (y : BinCfg (circ.n0 d + 1)),
        (1 / 2 : ℝ) * ∑ t : Bool, ∑ Y : BinCfg (circ.n0 d), unifOn (circ.omega d desc key) Y *
            (if (Fin.cons t (fun i => t == Y i) : BinCfg (circ.n0 d + 1)) = y then (1 : ℝ) else 0) =
          unifOn ((hatSource circ.toSource).omega d desc key) y) := by
  exact p7b_theorem_5_1_from_waters_prime p7b_waters_prime
