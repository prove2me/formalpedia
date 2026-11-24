-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.annihilator_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:17.156627+00:00
-- url     : https://prove2.me/submissions/2495874d-fbbd-4f6d-9e8d-672aa4bf9dce

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_trace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_inj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_index_piO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : AnnihSize := by
  intro o O S _ _ _ _ _ _ _ ϖ pr τ ψ q N i hU hϖ hq hq2 hpr hker hiN hτ hψ
  classical
  obtain ⟨T, hT⟩ := unram_trace hU
  have hψT : ∀ y, ψ (pr y) = τ (T y) := fun y => hψ y (T y) (hT y)
  have hTsm : ∀ (c : o) (y : O), T (algebraMap o O c * y) = c * T y := fun c y => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj := unram_inj hU
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  have hcancel : ∀ (k : ℕ) (x y : O), algebraMap o O (ϖ ^ k) * x = algebraMap o O (ϖ ^ k) * y → x = y := by
    intro k x y hxy
    rw [← Algebra.smul_def, ← Algebra.smul_def] at hxy
    exact smul_right_injective O (pow_ne_zero k hϖ0) hxy
  constructor
  · have h1 : pr.toAddMonoidHom.ker = piO O ϖ N := by
      ext y
      rw [AddMonoidHom.mem_ker]
      exact hker y
    rw [← index_piO hU ϖ hϖ q hq N, ← h1, AddSubgroup.index_ker,
      AddMonoidHom.range_eq_top.2 hpr]
    exact (Nat.card_congr (Equiv.Set.univ S)).symm
  · let g : O →+ S := pr.toAddMonoidHom.comp (AddMonoidHom.mulLeft (algebraMap o O (ϖ ^ i)))
    have hg : ∀ y, g y = pr (algebraMap o O (ϖ ^ i) * y) := fun y => rfl
    have hgker : g.ker = piO O ϖ (N - i) := by
      ext y
      rw [AddMonoidHom.mem_ker, hg, hker]
      have e : ϖ ^ N = ϖ ^ i * ϖ ^ (N - i) := by rw [← pow_add]; congr 1; omega
      constructor
      · rintro ⟨z, hz⟩
        refine ⟨z, hcancel i _ _ ?_⟩
        rw [hz, e, map_mul, mul_assoc]
      · rintro ⟨z, rfl⟩
        exact ⟨z, by rw [e, map_mul, mul_assoc]⟩
    have hrange : ∀ y : S, (∀ c, ψ (c * y) = 1) ↔ y ∈ g.range := by
      intro y
      constructor
      · intro hy
        obtain ⟨Y0, rfl⟩ := hpr y
        have h1 : ∀ c' : O, ∃ d, T (c' * Y0) = ϖ ^ i * d := by
          intro c'
          by_cases ht : T (c' * Y0) = 0
          · exact ⟨0, by rw [ht, mul_zero]⟩
          · obtain ⟨k, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht hϖ
            have h3 : ∀ x, τ (ϖ ^ k * x) = 1 := by
              intro x
              have h4 := hy (pr (algebraMap o O (((w⁻¹ : oˣ) : o) * x) * c'))
              rw [← map_mul, hψT, mul_assoc, hTsm, hw] at h4
              rw [← h4]
              congr 1
              have : ((w⁻¹ : oˣ) : o) * (w : o) = 1 := Units.inv_mul w
              linear_combination (-(x * ϖ ^ k)) * this
            have hik := (hτ k).2 h3
            refine ⟨(w : o) * ϖ ^ (k - i), ?_⟩
            rw [hw]
            have e : ϖ ^ k = ϖ ^ i * ϖ ^ (k - i) := by rw [← pow_add]; congr 1; omega
            rw [e]; ring
        let b := Module.Free.chooseBasis o O
        have h5 : ∀ j, ∃ d, b.repr Y0 j = ϖ ^ i * d := by
          intro j
          obtain ⟨bj, hbj⟩ := hU.tr_perfect (b.coord j)
          have h6 := hbj Y0
          rw [mul_comm Y0 (star bj), ← hT, Module.Basis.coord_apply] at h6
          rw [hinj h6]
          exact h1 _
        choose d hd using h5
        refine ⟨∑ j, d j • b j, ?_⟩
        rw [hg]
        congr 1
        conv_rhs => rw [← b.sum_repr Y0]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hd j, mul_smul, ← Algebra.smul_def]
      · rintro ⟨z, rfl⟩ c
        obtain ⟨c', rfl⟩ := hpr c
        rw [hg, ← map_mul, hψT, mul_left_comm, hTsm]
        exact (hτ i).1 le_rfl _
    have hcard : Nat.card {y : S // ∀ c, ψ (c * y) = 1} = Nat.card g.range :=
      Nat.card_congr (Equiv.subtypeEquivRight hrange)
    rw [hcard, ← AddSubgroup.index_ker, hgker, index_piO hU ϖ hϖ q hq]
end Formalism.HermitianLatticeCounting.P.S4aux
