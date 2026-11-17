-- Prove2me | solution 1 for CritWinSpin.p4c_1_1_ii_ppt_wrappers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-16T09:55:35.489303+00:00
-- url     : https://prove2.me/submissions/f247199e-34be-4001-a648-c2c052129102
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_RandMachine
import Definitions.Def_CritWinSpin_BilinearFamily
import Definitions.Def_CritWinSpin_errExt
import Definitions.Def_CritWinSpin_Lhat
import Theorems.Thm_CritWinSpin_p4c_1_1_ii_effpoly
import Theorems.Thm_CritWinSpin_p4c_1_1_ii_ppt_comb

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

theorem p4c_1_1_ii_ppt_wrappers_decomp :
    (∀ a b c : ℕ, EffPoly (fun d => a * d ^ b + c)) ∧
    (∀ (S : SpinLaw) (p Ac Cc : ℕ) (F : BilinearFamily) (src : BinarySource F)
      (liftF : Str → Str), CookPvsNP.PolyTimeComputable liftF →
      ∀ (û : (d : ℕ) → (desc : Str) → WatersKey F desc d → ℚ) (d₁ : ℕ), 1 ≤ d₁ →
      (∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
        liftF (encInst (src.ham d desc key)) =
          tupleCode [encInst (liftInst S p Ac Cc (src.ham d desc key) (û d desc key)),
            encRat (û d desc key)]) →
      ∃ Fam : PPT,
        (∀ d, 1 ≤ d → d < d₁ → ∀ ω : Fin (Fam.coins.eval (unary d).length) → Bool,
          Fam.alg (tupleCode [List.ofFn ω, unary d]) =
            encInst ((0 : Matrix (Fin (src.n d * cloudSize p Cc (src.n d))) (Fin (src.n d * cloudSize p Cc (src.n d))) ℚ),
              (0 : Fin (src.n d * cloudSize p Cc (src.n d)) → ℚ))) ∧
        (∀ d ≥ d₁,
          (∀ ω : Fin (Fam.coins.eval (unary d).length) → Bool,
            ∃ desc key, GenSupport F.gen d desc ∧
              Fam.alg (tupleCode [List.ofFn ω, unary d]) =
                encInst (liftInst S p Ac Cc (src.ham d desc key) (û d desc key))) ∧
          (let Pi₀ := keyLiftLaw F d fun desc key => liftInst S p Ac Cc (src.ham d desc key) (û d desc key)
           let Pi₁ := famLaw Fam (src.n d * cloudSize p Cc (src.n d)) d
           (∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M) ∧
           Pi₁.supp ⊆ Pi₀.supp ∧
           (∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0) ∧
           ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M| ≤ 1 / (2 : ℝ) ^ d))) ∧
    (∀ (S : SpinLaw) (Nf k D : ℕ → ℕ),
      (∀ d, 1 ≤ k d) → ∀ (hkD : ∀ d, k d ≤ D d), PolyBounded D → ∀ (A : PPT),
      ∃ (A'_ext A'_amp : PPT) (w : ℕ → ℝ)
        (R_ext : (d : ℕ) → Inst (Nf d) → (Fin (D d) → Config S (Fin (Nf d))) → Option (Config S (Fin (Nf d))) → ℝ)
        (R_amp : (d : ℕ) → Inst (Nf d) → (Fin (D d) → Config S (Fin (Nf d))) → Option (Fin (D d + 1) → Config S (Fin (Nf d))) → ℝ),
        (∀ d, 1 / (2 * (D d : ℝ)) ≤ w d ∧ w d ≤ 1) ∧
        (∀ d M X o, 0 ≤ R_ext d M X o) ∧ (∀ d M X, ∑ o, R_ext d M X o = 1) ∧
        (∀ d M X o, 0 ≤ R_amp d M X o) ∧ (∀ d M X, ∑ o, R_amp d M X o = 1) ∧
        (∀ d M X o,
          A'_ext.prob (tupleCode [encInst M, encSamples X]) (fun s => decConfig S (Nf d) s = o) =
            w d * A.prob (tupleCode [encInst M, encSamples (fun j : Fin (k d) => X ⟨j.1, lt_of_lt_of_le j.2 (hkD d)⟩)])
              (fun s => decConfig S (Nf d) s = o) + (1 - w d) * R_ext d M X o) ∧
        (∀ d M X o,
          A'_amp.prob (tupleCode [encInst M, encSamples X]) (fun s => decTuple S (Nf d) (D d + 1) s = o) =
            w d * (∑ y : Option (Fin (k d + 1) → Config S (Fin (Nf d))),
              (if Option.map (fun Y (j : Fin (D d + 1)) =>
                  if h : j.1 < k d + 1 then Y ⟨j.1, h⟩ else X ⟨k d + (j.1 - (k d + 1)), by have := hkD d; omega⟩) y = o
                then (1 : ℝ) else 0) *
                A.prob (tupleCode [encInst M, encSamples (fun j : Fin (k d) => X ⟨j.1, lt_of_lt_of_le j.2 (hkD d)⟩)])
                  (fun s => decTuple S (Nf d) (k d + 1) s = y)) +
            (1 - w d) * R_amp d M X o)) :=
  ⟨p4c_1_1_ii_effpoly, p4c_1_1_ii_ppt_comb.1, p4c_1_1_ii_ppt_comb.2⟩

end CritWinSpin

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

theorem solution :
    (∀ a b c : ℕ, EffPoly (fun d => a * d ^ b + c)) ∧
    (∀ (S : CritWinSpin.SpinLaw) (p Ac Cc : ℕ) (F : CritWinSpin.BilinearFamily) (src : CritWinSpin.BinarySource F)
      (liftF : Str → Str), CookPvsNP.PolyTimeComputable liftF →
      ∀ (û : (d : ℕ) → (desc : Str) → CritWinSpin.WatersKey F desc d → ℚ) (d₁ : ℕ), 1 ≤ d₁ →
      (∀ d ≥ d₁, ∀ desc, CritWinSpin.GenSupport F.gen d desc → ∀ key : CritWinSpin.WatersKey F desc d,
        liftF (CritWinSpin.encInst (src.ham d desc key)) =
          tupleCode [CritWinSpin.encInst (CritWinSpin.liftInst S p Ac Cc (src.ham d desc key) (û d desc key)),
            encRat (û d desc key)]) →
      ∃ Fam : PPT,
        (∀ d, 1 ≤ d → d < d₁ → ∀ ω : Fin (Fam.coins.eval (unary d).length) → Bool,
          Fam.alg (tupleCode [List.ofFn ω, unary d]) =
            CritWinSpin.encInst ((0 : Matrix (Fin (src.n d * CritWinSpin.cloudSize p Cc (src.n d))) (Fin (src.n d * CritWinSpin.cloudSize p Cc (src.n d))) ℚ),
              (0 : Fin (src.n d * CritWinSpin.cloudSize p Cc (src.n d)) → ℚ))) ∧
        (∀ d ≥ d₁,
          (∀ ω : Fin (Fam.coins.eval (unary d).length) → Bool,
            ∃ desc key, CritWinSpin.GenSupport F.gen d desc ∧
              Fam.alg (tupleCode [List.ofFn ω, unary d]) =
                CritWinSpin.encInst (CritWinSpin.liftInst S p Ac Cc (src.ham d desc key) (û d desc key))) ∧
          (let Pi₀ := CritWinSpin.keyLiftLaw F d fun desc key => CritWinSpin.liftInst S p Ac Cc (src.ham d desc key) (û d desc key)
           let Pi₁ := CritWinSpin.famLaw Fam (src.n d * CritWinSpin.cloudSize p Cc (src.n d)) d
           (∀ M ∈ Pi₁.supp, 0 ≤ Pi₁.prob M) ∧
           Pi₁.supp ⊆ Pi₀.supp ∧
           (∀ M ∈ Pi₀.supp, M ∉ Pi₁.supp → Pi₁.prob M = 0) ∧
           ∑ M ∈ Pi₀.supp, |Pi₁.prob M - Pi₀.prob M| ≤ 1 / (2 : ℝ) ^ d))) ∧
    (∀ (S : CritWinSpin.SpinLaw) (Nf k D : ℕ → ℕ),
      (∀ d, 1 ≤ k d) → ∀ (hkD : ∀ d, k d ≤ D d), PolyBounded D → ∀ (A : PPT),
      ∃ (A'_ext A'_amp : PPT) (w : ℕ → ℝ)
        (R_ext : (d : ℕ) → CritWinSpin.Inst (Nf d) → (Fin (D d) → CritWinSpin.Config S (Fin (Nf d))) → Option (CritWinSpin.Config S (Fin (Nf d))) → ℝ)
        (R_amp : (d : ℕ) → CritWinSpin.Inst (Nf d) → (Fin (D d) → CritWinSpin.Config S (Fin (Nf d))) → Option (Fin (D d + 1) → CritWinSpin.Config S (Fin (Nf d))) → ℝ),
        (∀ d, 1 / (2 * (D d : ℝ)) ≤ w d ∧ w d ≤ 1) ∧
        (∀ d M X o, 0 ≤ R_ext d M X o) ∧ (∀ d M X, ∑ o, R_ext d M X o = 1) ∧
        (∀ d M X o, 0 ≤ R_amp d M X o) ∧ (∀ d M X, ∑ o, R_amp d M X o = 1) ∧
        (∀ d M X o,
          A'_ext.prob (tupleCode [CritWinSpin.encInst M, CritWinSpin.encSamples X]) (fun s => CritWinSpin.decConfig S (Nf d) s = o) =
            w d * A.prob (tupleCode [CritWinSpin.encInst M, CritWinSpin.encSamples (fun j : Fin (k d) => X ⟨j.1, lt_of_lt_of_le j.2 (hkD d)⟩)])
              (fun s => CritWinSpin.decConfig S (Nf d) s = o) + (1 - w d) * R_ext d M X o) ∧
        (∀ d M X o,
          A'_amp.prob (tupleCode [CritWinSpin.encInst M, CritWinSpin.encSamples X]) (fun s => CritWinSpin.decTuple S (Nf d) (D d + 1) s = o) =
            w d * (∑ y : Option (Fin (k d + 1) → CritWinSpin.Config S (Fin (Nf d))),
              (if Option.map (fun Y (j : Fin (D d + 1)) =>
                  if h : j.1 < k d + 1 then Y ⟨j.1, h⟩ else X ⟨k d + (j.1 - (k d + 1)), by have := hkD d; omega⟩) y = o
                then (1 : ℝ) else 0) *
                A.prob (tupleCode [CritWinSpin.encInst M, CritWinSpin.encSamples (fun j : Fin (k d) => X ⟨j.1, lt_of_lt_of_le j.2 (hkD d)⟩)])
                  (fun s => CritWinSpin.decTuple S (Nf d) (k d + 1) s = y)) +
            (1 - w d) * R_amp d M X o)) :=
  CritWinSpin.p4c_1_1_ii_ppt_wrappers_decomp
