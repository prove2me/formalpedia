-- Prove2me | solution 1 for Formalism.BehrendSets.Stab.sub_one_le_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:15.248692+00:00
-- url     : https://prove2.me/submissions/a1e6b689-2a5a-4112-86c4-a621f8f1b402

import Definitions.Def_Formalism_BehrendSets_StatementE
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TotientLeOfIsPrimitiveRoot
import Theorems.Thm_Formalism_BehrendSets_Stab_totient_le_of_isPrimitiveRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Module Matrix
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Stab
namespace Formalism.BehrendSets.Stab
theorem _root_.solution {E : Type} [Field E] [NumberField E] {k g : ℕ} (hg : g.Prime)
    (M : Matrix (Fin k) (Fin k) E) (hM : M ^ g = 1) (hM1 : M ≠ 1) :
    g - 1 ≤ finrank ℚ E * k := by
  have := Fact.mk hg
  have hint : IsIntegral E M := IsIntegral.of_finite E M
  have hμ0 : minpoly E M ≠ 0 := minpoly.ne_zero hint
  have hdvd : minpoly E M ∣ cyclotomic g E * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hM]
  have hnc : ¬ IsCoprime (minpoly E M) (cyclotomic g E) := by
    intro hc
    have h1 : minpoly E M ∣ X - 1 := hc.dvd_of_dvd_mul_left hdvd
    have h2 := aeval_eq_zero_of_dvd_aeval_eq_zero h1 (minpoly.aeval E M)
    apply hM1
    simpa [sub_eq_zero] using h2
  obtain ⟨q, hq, hqμ, hqΦ⟩ : ∃ q, Irreducible q ∧ q ∣ minpoly E M ∧ q ∣ cyclotomic g E := by
    by_contra h
    push Not at h
    exact hnc (isCoprime_of_irreducible_dvd (fun h' => hμ0 h'.1) fun z hz h1 h2 => h z hz h1 h2)
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqdeg : q.natDegree ≤ k := by
    calc q.natDegree ≤ (minpoly E M).natDegree := natDegree_le_of_dvd hqμ hμ0
      _ ≤ M.charpoly.natDegree :=
          natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly M) (Matrix.charpoly_monic M).ne_zero
      _ = k := by rw [Matrix.charpoly_natDegree_eq_dim]; simp
  have : Fact (Irreducible q) := ⟨hq⟩
  let pb := AdjoinRoot.powerBasis hq0
  have : FiniteDimensional E (AdjoinRoot q) := pb.finite
  have hfin : finrank E (AdjoinRoot q) = q.natDegree := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim]
  have hroot : aeval (AdjoinRoot.root q) (cyclotomic g E) = 0 :=
    aeval_eq_zero_of_dvd_aeval_eq_zero hqΦ (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
  have : CharZero (AdjoinRoot q) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have : NeZero (g : AdjoinRoot q) := ⟨Nat.cast_ne_zero.mpr hg.ne_zero⟩
  have hprim : IsPrimitiveRoot (AdjoinRoot.root q) g := by
    rw [← isRoot_cyclotomic_iff, ← map_cyclotomic g (algebraMap E (AdjoinRoot q)), IsRoot,
      eval_map, ← aeval_def]
    exact hroot
  have h3 := totient_le_of_isPrimitiveRoot (E := E) hg.pos hprim
  rw [Nat.totient_prime hg, hfin] at h3
  exact h3.trans (Nat.mul_le_mul_left _ hqdeg)
end Formalism.BehrendSets.Stab
