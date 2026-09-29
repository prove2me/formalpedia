-- Prove2me | solution 1 for CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/23aca388-1a6d-5108-a3d8-488cb6d9ac91

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime
import Theorems.Thm_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false

noncomputable section

namespace CoprimeLevelSol

open CongruenceSubgroup
open scoped MatrixGroups

variable {k : ℤ}

lemma qCoeff_zero_form (L : ℕ) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (Gamma1 L) k)) n = 0 := by
  show (UpperHalfPlane.qExpansion 1 ⇑(0 : CuspForm (Gamma1 L) k)).coeff n = 0
  rw [CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero]; simp

lemma forall_qCoeff_eq_zero_of_aux (Q : Finset ℕ) :
    ∀ (L : ℕ) [NeZero L] (h : CuspForm (Gamma1 L) k),
      (∀ q ∈ Q, q.Prime ∧ ¬ q ∣ L) →
      (∀ n : ℕ, (∀ q ∈ Q, ¬ q ∣ n) → ModularFormClass.qCoeff h n = 0) →
      ∀ n : ℕ, ModularFormClass.qCoeff h n = 0 := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro L _ h _ hh n
    exact hh n (fun q hq => (Finset.notMem_empty q hq).elim)
  | insert p Q hpQ ih =>
    intro L _ h hQ hh
    have hp : p.Prime := (hQ p (Finset.mem_insert_self p Q)).1
    have hpL : ¬ p ∣ L := (hQ p (Finset.mem_insert_self p Q)).2
    haveI : NeZero (L * p ^ 2) := ⟨mul_ne_zero (NeZero.ne L) (pow_ne_zero 2 hp.ne_zero)⟩

    obtain ⟨g, hg⟩ := CuspForm.exists_gamma1_qCoeff_eq_ite_coprime L k h p hp.ne_zero
      (L * p ^ 2) dvd_rfl
    have hQ' : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ L * p ^ 2 := by
      intro q hq
      have hq' := hQ q (Finset.mem_insert_of_mem hq)
      refine ⟨hq'.1, fun hdvd => ?_⟩
      rcases (Nat.Prime.dvd_mul hq'.1).mp hdvd with h1 | h1
      · exact hq'.2 h1
      · have := (Nat.prime_dvd_prime_iff_eq hq'.1 hp).mp (hq'.1.dvd_of_dvd_pow h1)
        exact hpQ (this ▸ hq)
    have hg0 : ∀ n : ℕ, (∀ q ∈ Q, ¬ q ∣ n) → ModularFormClass.qCoeff g n = 0 := by
      intro n hn
      rw [hg n]
      split_ifs with hcop
      · refine hh n fun q hq => ?_
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop.symm
        · exact hn q hq
      · rfl
    have hgall : ∀ n, ModularFormClass.qCoeff g n = 0 := ih (L * p ^ 2) g hQ' hg0

    have hsupp : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff h n = 0 := by
      intro n hn
      have := hgall n
      rw [hg n, if_pos (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn))] at this
      exact this
    have h0 : h = 0 := CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero k hp hpL h hsupp
    intro n
    rw [h0]
    exact qCoeff_zero_form L n

theorem main (N : ℕ) [NeZero N] (K : ℕ) (hK : K ≠ 0) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0)
    (n : ℕ) (hn : Nat.Coprime n N) : ModularFormClass.qCoeff f n = 0 := by
  classical
  haveI : NeZero (N * N ^ 2) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (NeZero.ne N))⟩

  obtain ⟨g, hg⟩ := CuspForm.exists_gamma1_qCoeff_eq_ite_coprime N k f N (NeZero.ne N)
    (N * N ^ 2) dvd_rfl

  set Q : Finset ℕ := K.primeFactors.filter (fun q => ¬ q ∣ N) with hQdef
  have hQ : ∀ q ∈ Q, q.Prime ∧ ¬ q ∣ N * N ^ 2 := by
    intro q hq
    rw [hQdef, Finset.mem_filter] at hq
    have hqpr : q.Prime := Nat.prime_of_mem_primeFactors hq.1
    refine ⟨hqpr, fun hdvd => hq.2 ?_⟩
    rcases (Nat.Prime.dvd_mul hqpr).mp hdvd with h1 | h1
    · exact h1
    · exact hqpr.dvd_of_dvd_pow h1
  have hg0 : ∀ m : ℕ, (∀ q ∈ Q, ¬ q ∣ m) → ModularFormClass.qCoeff g m = 0 := by
    intro m hm
    rw [hg m]
    split_ifs with hcop
    · apply hf
      refine Nat.coprime_of_dvd fun q hq hqm hqK => ?_
      by_cases hqN : q ∣ N
      · exact (Nat.Prime.coprime_iff_not_dvd hq).mp (Nat.Coprime.coprime_dvd_left hqm hcop) hqN
      · have hqQ : q ∈ Q := by
          rw [hQdef, Finset.mem_filter]
          exact ⟨Nat.mem_primeFactors.mpr ⟨hq, hqK, hK⟩, hqN⟩
        exact hm q hqQ hqm
    · rfl
  have hgall := forall_qCoeff_eq_zero_of_aux Q (N * N ^ 2) g hQ hg0
  have := hgall n
  rw [hg n, if_pos hn] at this
  exact this

end CoprimeLevelSol

end

open CongruenceSubgroup in
theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0)
    (n : ℕ) (hn : Nat.Coprime n N) : ModularFormClass.qCoeff f n = 0 :=
  CoprimeLevelSol.main N K hK f hf n hn

end S_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero
end P2MW
export P2MW.S_CuspForm_qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero (solution)
