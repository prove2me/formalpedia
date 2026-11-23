-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.tieF_pow_apply_eq_zero_of_min_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:56.172801+00:00
-- url     : https://prove2.me/submissions/3fcad11e-11ca-4f9c-b503-edfa04b35a27

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)
private lemma add_single_mem_support_of_mem_support_pderiv (i : σ) (p : MvPolynomial σ k) (t : σ →₀ ℕ) (ht : t ∈ (pderiv i p).support) :
    t + Finsupp.single i 1 ∈ p.support := by
  classical
  have hp : pderiv i p = ∑ s ∈ p.support, pderiv i (monomial s (coeff s p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [MvPolynomial.mem_support_iff, hp, MvPolynomial.coeff_sum] at ht
  obtain ⟨s, hs, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  rw [pderiv_monomial, MvPolynomial.coeff_monomial] at hne
  split_ifs at hne with hst
  · have hsi : s i ≠ 0 := by
      intro h0
      apply hne
      rw [h0]
      simp
    have hts : t + Finsupp.single i 1 = s := by
      rw [← hst]
      ext j
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h
        omega
      · omega
    rw [hts]
    exact hs
  · exact absurd rfl hne
end
end Formalism.InvariantFactorPaths.KP.LL
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution [CharZero k] (hw : Function.Injective w) (he : Function.Injective e)
    (hwe : ∀ c d, w c ≠ e d) {o n : ℕ} {x : MvPolynomial σ k} (hx : BiHom w e o n x) :
    ∀ m, min o n < m → (tieF w e ^ m) x = 0 := by
  classical
  have hsupp : ∀ (y : MvPolynomial σ k) (t : σ →₀ ℕ), t ∈ (tieF w e y).support →
      ∃ c, t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 ∈ y.support := by
    intro y t ht
    have key : tieF w e y = ∑ c, pderiv (w c) (pderiv (e c) y) := by simp [tieF]
    rw [key] at ht
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
    exact ⟨c, add_single_mem_support_of_mem_support_pderiv _ _ _ (add_single_mem_support_of_mem_support_pderiv _ _ _ hc)⟩
  have hW1 : ∀ (t : σ →₀ ℕ) (c : Fin r),
      (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (w d)) = (∑ d, t (w d)) + 1 := by
    intro t c
    have h1 : ∀ d, (e c = w d) ↔ False := fun d => ⟨fun h => hwe d c h.symm, False.elim⟩
    simp [Finsupp.single_apply, hw.eq_iff, Finset.sum_add_distrib, h1]
  have hE1 : ∀ (t : σ →₀ ℕ) (c : Fin r),
      (∑ d, (t + Finsupp.single (w c) 1 + Finsupp.single (e c) 1 : σ →₀ ℕ) (e d)) = (∑ d, t (e d)) + 1 := by
    intro t c
    have h1 : ∀ d, (w c = e d) ↔ False := fun d => ⟨fun h => hwe c d h, False.elim⟩
    simp [Finsupp.single_apply, he.eq_iff, Finset.sum_add_distrib, h1]
  have claim : ∀ (j : ℕ) (t : σ →₀ ℕ), t ∈ ((tieF w e ^ j) x).support →
      (∑ d, t (w d)) + j = o ∧ (∑ d, t (e d)) + j = n := by
    intro j
    induction j with
    | zero =>
      intro t ht
      have ht' : t ∈ x.support := by simpa using ht
      simpa using hx t ht'
    | succ j ih =>
      intro t ht
      have ht' : t ∈ (tieF w e ((tieF w e ^ j) x)).support := by
        rw [pow_succ'] at ht
        exact ht
      obtain ⟨c, hc⟩ := hsupp _ t ht'
      obtain ⟨h1, h2⟩ := ih _ hc
      rw [hW1] at h1
      rw [hE1] at h2
      constructor <;> omega
  intro m hm
  by_contra hne
  obtain ⟨t, ht⟩ := MvPolynomial.ne_zero_iff.mp hne
  obtain ⟨h1, h2⟩ := claim m t (MvPolynomial.mem_support_iff.mpr ht)
  omega
end Formalism.InvariantFactorPaths.KP.LL
