-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.fib_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:07.622825+00:00
-- url     : https://prove2.me/submissions/142f1b0e-bdf8-4b14-add3-c54d62f4f9b1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_sum_eq_zero_of_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_sum_card_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_latZ_mul_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_matrixHeart
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_base_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_orbZ_rep_eq_base_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_exists_injective_shift_of_orbZ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K)
open Classical
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hfin : ∀ (m : ℕ) (Z : Matrix (Fin m) (Fin m) K), IsInt R Z → IsUnit Z.det →
      Finite (coker R Z))
    (w w' : Point K) (k : ℕ) (hn : w.1.sum = w'.1.sum) (hkn : k + 2 ≤ w.1.sum)
    (Q : Finset (Cos R w × Cos R w'))
    (hQ : ∀ q, q ∈ Q ↔ IsInt R (orbZ w (rep R q.1)) ∧ IsInt R (orbZ w' (rep R q.2))) (y) (y')
    (he : ∀ a b : Fin w.1.sum, k < a.val → b.val + 1 = w.1.sum → (base R k w y)⁻¹ a b = 0)
    (he' : ∀ a b : Fin w'.1.sum, k < a.val → b.val + 1 = w'.1.sum →
      (base R k w' y')⁻¹ a b = 0) :
    ∑ q ∈ Q with (kap R k w q.1 = y ∧ kap R k w' q.2 = y'),
      (badN R k w w' q : ℂ) * (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) = 0 := by
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by
    have := (hsd 1).2 R.one_mem r hr
    simpa using this
  have hbd := base_det R k w y
  have hbd' := base_det R k w' y'
  obtain ⟨X, rel, hcnt, hshift⟩ := matrixHeart R ψ hsd hfin w.1.sum w'.1.sum hn k hkn
    (base R k w y) (base R k w' y') hbd hbd' he he'
  have hdetp : ∀ (N : ℕ) (B p : Matrix (Fin N) (Fin N) K), IsUnit B.det → IsPP R k p →
      IsUnit (B * p).det := by
    intro N B p hB hp
    rw [Matrix.det_mul, isUpUni_det K hp.1.1, mul_one]; exact hB

  have hb : ∀ q ∈ Q.filter (fun q => kap R k w q.1 = y ∧ kap R k w' q.2 = y'),
      Nonempty ({φ : coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2)) //
        φ ∈ isoZZ R (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) ∧
          InTT R (k + 1) (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ ∧
          ¬ InTT R k (orbZ w (rep R q.1)) (orbZ w' (rep R q.2)) φ} ≃
        {x : X // rel x (latZ R (orbZ w (rep R q.1))) (latZ R (orbZ w' (rep R q.2)))}) ∧
      Finite (coker R (orbZ w (rep R q.1))) ∧ Finite (coker R (orbZ w' (rep R q.2))) := by
    intro q hq
    rw [Finset.mem_filter, hQ] at hq
    obtain ⟨⟨hi, hi'⟩, hy, hy'⟩ := hq
    obtain ⟨p, hp, e⟩ := orbZ_rep_eq_base_mul R k w y q.1 hy
    obtain ⟨p', hp', e'⟩ := orbZ_rep_eq_base_mul R k w' y' q.2 hy'
    rw [e] at hi ⊢
    rw [e'] at hi' ⊢
    exact ⟨hcnt p p' hp hp' hi hi', hfin _ _ hi (hdetp _ _ _ hbd hp),
      hfin _ _ hi' (hdetp _ _ _ hbd' hp')⟩
  have hsum : ∑ q ∈ Q with (kap R k w q.1 = y ∧ kap R k w' q.2 = y'),
      (badN R k w w' q : ℂ) * (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) =
      ∑ q ∈ Q with (kap R k w q.1 = y ∧ kap R k w' q.2 = y'),
      (Nat.card {x : X // rel x (latZ R (orbZ w (rep R q.1))) (latZ R (orbZ w' (rep R q.2)))} : ℂ)
        * (phase ψ (rep R q.1) * conj (phase ψ (rep R q.2))) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨⟨e⟩, -, -⟩ := hb q hq
    rw [badN, Nat.card_congr e]
  have key := sum_card_eq_zero (Q.filter (fun q => kap R k w q.1 = y ∧ kap R k w' q.2 = y'))
    (fun q => phase ψ (rep R q.1) * conj (phase ψ (rep R q.2)))
    (fun x q => rel x (latZ R (orbZ w (rep R q.1))) (latZ R (orbZ w' (rep R q.2))))
    (by
      intro q hq
      obtain ⟨⟨e⟩, f1, f2⟩ := hb q hq
      have : Finite (coker R (orbZ w (rep R q.1)) ≃ₗ[R] coker R (orbZ w' (rep R q.2))) :=
        Finite.of_injective (fun φ => (φ : coker R (orbZ w (rep R q.1)) →
          coker R (orbZ w' (rep R q.2)))) DFunLike.coe_injective
      exact Finite.of_equiv _ e
    )
    (by
      intro x
      obtain ⟨σ, σ', hσ, hσ', hζ, hsh⟩ := hshift x
      obtain ⟨S, hSinj, hS⟩ := exists_injective_shift_of_orbZ R k ψ hψ w y σ hσ
      obtain ⟨S', hSinj', hS'⟩ := exists_injective_shift_of_orbZ R k ψ hψ w' y' σ' hσ'
      refine sum_eq_zero_of_shift _ _ (Prod.map S S') (hSinj.prodMap hSinj') ?_
        (ψ (sUp σ - sUp σ')) hζ ?_
      · intro q hq
        rw [Finset.mem_filter, Finset.mem_filter, hQ] at hq
        obtain ⟨⟨⟨hi, hi'⟩, hy, hy'⟩, hr⟩ := hq
        obtain ⟨p, hp, e⟩ := orbZ_rep_eq_base_mul R k w y q.1 hy
        obtain ⟨p', hp', e'⟩ := orbZ_rep_eq_base_mul R k w' y' q.2 hy'
        obtain ⟨hk1, -, h3⟩ := hS q.1 hy
        obtain ⟨hk1', -, h3'⟩ := hS' q.2 hy'
        obtain ⟨g, hg, hgi, eg⟩ := h3 p e
        obtain ⟨g', hg', hgi', eg'⟩ := h3' p' e'
        rw [e] at hi hr
        rw [e'] at hi' hr
        obtain ⟨j1, j2, j3⟩ := hsh p p' hp hp' hi hi' hr
        rw [Finset.mem_filter, Finset.mem_filter, hQ]
        simp only [Prod.map_fst, Prod.map_snd]
        rw [eg, eg', latZ_mul_int R _ g hg hgi, latZ_mul_int R _ g' hg' hgi']
        exact ⟨⟨⟨Formalism.DoubleCosetMeasures.P.isInt_mul R j1 hgi, Formalism.DoubleCosetMeasures.P.isInt_mul R j2 hgi'⟩, hk1, hk1'⟩, j3⟩
      · intro q hq
        rw [Finset.mem_filter, Finset.mem_filter] at hq
        obtain ⟨⟨-, hy, hy'⟩, -⟩ := hq
        obtain ⟨-, h2, -⟩ := hS q.1 hy
        obtain ⟨-, h2', -⟩ := hS' q.2 hy'
        simp only [Prod.map_fst, Prod.map_snd]
        rw [h2, h2', map_mul, hun (sUp σ'), sub_eq_add_neg, AddChar.map_add_eq_mul]
        ring
    )
  rw [hsum]
  exact key
end Formalism.FourierDecayAlt.P.A5x9
