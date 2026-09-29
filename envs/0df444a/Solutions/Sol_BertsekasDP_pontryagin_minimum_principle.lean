-- Prove2me | solution 1 for BertsekasDP.pontryagin_minimum_principle
-- status  : ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-07T20:54:42.240991+00:00
-- url     : https://prove2.me/submissions/8e3e2c5e-7770-43e8-a75f-62c53b79a8f7

import Theorems.Thm_BertsekasDP_piecewise_adjoint_terminal_exists
import Theorems.Thm_BertsekasDP_needle_cost_first_variation
import Theorems.Thm_BertsekasDP_minimized_hamiltonian_extension

open Set Filter
open scoped Topology

/- A finite exceptional set cannot allow a continuous function with zero
derivative elsewhere to change value. Continuity joins the adjacent intervals. -/
private theorem eq_endpoints_of_deriv_zero_off_finset
    (E : ℝ → ℝ) (F : Finset ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn E (Icc a b))
    (hd : ∀ t ∈ Ioo a b \ (F : Set ℝ), HasDerivAt E 0 t) : E b = E a := by
  classical
  induction F using Finset.induction_on generalizing a b with
  | empty =>
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
      (fun t ht => hd t ⟨ht, by simp⟩) (intervalIntegrable_const (c := (0 : ℝ)))
    simpa using (sub_eq_zero.mp (by simpa using h.symm) : E b = E a)
  | @insert c F hcF ih =>
    by_cases hci : c ∈ Ioo a b
    · have hleft : E c = E a := ih a c hci.1.le
        (hc.mono (Icc_subset_Icc_right hci.2.le)) (by
          intro t ht
          apply hd t
          exact ⟨⟨ht.1.1, ht.1.2.trans hci.2⟩, by
            simpa only [Finset.coe_insert, mem_insert_iff, not_or] using
              And.intro (ne_of_lt ht.1.2) ht.2⟩)
      have hright : E b = E c := ih c b hci.2.le
        (hc.mono (Icc_subset_Icc_left hci.1.le)) (by
          intro t ht
          apply hd t
          exact ⟨⟨hci.1.trans ht.1.1, ht.1.2⟩, by
            simpa only [Finset.coe_insert, mem_insert_iff, not_or] using
              And.intro (ne_of_gt ht.1.1) ht.2⟩)
      exact hright.trans hleft
    · apply ih a b hab hc
      intro t ht
      apply hd t
      refine ⟨ht.1, ?_⟩
      have htc : t ≠ c := fun heq => hci (heq ▸ ht.1)
      simpa only [Finset.coe_insert, mem_insert_iff, not_or] using And.intro htc ht.2

theorem solution {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (hh : ContDiff ℝ 1 M.h)
    (ustar : ℝ → EuclideanSpace ℝ (Fin m))
    (xstar : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 ustar xstar)
    (hopt : ∀ u x, BertsekasCTAdmissibleFrom M 0 M.x0 u x →
      BertsekasCTCostFrom M 0 ustar xstar ≤ BertsekasCTCostFrom M 0 u x) :
    ∃ (p : ℝ → EuclideanSpace ℝ (Fin n)) (F : Finset ℝ) (c : ℝ),
      ContinuousOn p (Set.Icc 0 M.T) ∧
      p M.T = gradient M.h (xstar M.T) ∧
      (∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        HasDerivAt p
          (-gradient (fun y => BertsekasHamiltonian M y (ustar t) (p t)) (xstar t))
          t) ∧
      (∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        IsMinOn (fun u => BertsekasHamiltonian M (xstar t) u (p t)) M.U (ustar t)) ∧
      (∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        BertsekasHamiltonian M (xstar t) (ustar t) (p t) = c) := by
  classical
  obtain ⟨p, Fp, hp, hterm, hadj⟩ :=
    BertsekasDP.piecewise_adjoint_terminal_exists M hf hg ustar xstar
      hadm.2.1 hadm.2.2.1 (gradient M.h (xstar M.T))
  obtain ⟨Fu, hu⟩ := hadm.2.1.2
  obtain ⟨Fx, hstate⟩ := hadm.2.2.2.2
  let F : Finset ℝ := Fp ∪ Fu ∪ Fx ∪ {0, M.T}
  have hregular {t : ℝ} (ht : t ∈ Icc 0 M.T \ (F : Set ℝ)) :
      t ∈ Ioo 0 M.T ∧ t ∉ Fp ∧ t ∉ Fu ∧ t ∉ Fx := by
    have hn : t ∉ Fp ∧ t ∉ Fu ∧ t ∉ Fx ∧ t ≠ 0 ∧ t ≠ M.T := by
      simpa [F, not_or, and_assoc, and_left_comm, and_comm] using ht.2
    exact ⟨⟨lt_of_le_of_ne ht.1.1 hn.2.2.2.1.symm,
      lt_of_le_of_ne ht.1.2 hn.2.2.2.2⟩, hn.1, hn.2.1, hn.2.2.1⟩
  have hadjF : ∀ t ∈ Icc 0 M.T \ (F : Set ℝ),
      HasDerivAt p
        (-gradient (fun y => BertsekasHamiltonian M y (ustar t) (p t)) (xstar t)) t :=
    fun t ht => hadj t ⟨ht.1, (hregular ht).2.1⟩
  have huF : ContinuousOn ustar (Icc 0 M.T \ (F : Set ℝ)) :=
    hu.mono (fun t ht => ⟨ht.1, (hregular ht).2.2.1⟩)
  have hmin : ∀ t ∈ Icc 0 M.T \ (F : Set ℝ),
      IsMinOn (fun u => BertsekasHamiltonian M (xstar t) u (p t)) M.U (ustar t) := by
    intro t ht v hv
    have hrt := hregular ht
    have hut : ContinuousAt ustar t := hu.continuousAt
      (inter_mem (Icc_mem_nhds hrt.1.1 hrt.1.2)
        ((Fu.finite_toSet.isClosed.isOpen_compl).mem_nhds hrt.2.2.1))
    obtain ⟨xε, hεadm, hlim⟩ :=
      BertsekasDP.needle_cost_first_variation M hf hg hh ustar xstar p
        hadm hp hterm Fp hadj t hrt.1 hut v hv
    change BertsekasHamiltonian M (xstar t) (ustar t) (p t) ≤
      BertsekasHamiltonian M (xstar t) v (p t)
    apply sub_nonneg.mp
    apply ge_of_tendsto hlim
    filter_upwards [hεadm, self_mem_nhdsWithin] with ε hε hεpos
    exact div_nonneg (sub_nonneg.mpr (hopt _ _ hε)) (le_of_lt hεpos)
  obtain ⟨E, hEcont, hEeq, hEderiv⟩ :=
    BertsekasDP.minimized_hamiltonian_extension M hf hg ustar xstar p F
      hadm.1 hadm.2.1.1 huF hadm.2.2.1 hp
      (fun t ht => hstate t ⟨ht.1, (hregular ht).2.2.2⟩) hadjF hmin
  refine ⟨p, F, E 0, hp, hterm, hadjF, hmin, ?_⟩
  intro t ht
  rw [← hEeq t ht]
  apply eq_endpoints_of_deriv_zero_off_finset E F 0 t ht.1.1
    (hEcont.mono (Icc_subset_Icc_right ht.1.2))
  intro s hs
  exact hEderiv s ⟨⟨hs.1.1, hs.1.2.trans_le ht.1.2⟩, hs.2⟩
