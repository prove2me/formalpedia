-- Prove2me | solution 1 for CompOT.Metric.prop_2_2_pos
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:21:34.928839+00:00
-- url     : https://prove2.me/submissions/4bed5f70-d7a5-49f3-be64-bb060eb6b096

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

set_option autoImplicit false
open Matrix CompOT.Metric

theorem solution {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k)
    (a b : Fin n → ℝ) (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n))
    (hab : a ≠ b) :
    0 < W D p a b := by
  have hp0 : 0 < p := by linarith
  set U := CompOT.Assignment.couplings a b with hU
  have hcont : ∀ i j, Continuous fun P : Matrix (Fin n) (Fin n) ℝ => P i j :=
    fun i j => Continuous.matrix_elem continuous_id i j
  -- closedness
  have hclosed : IsClosed U := by
    have : U = ((⋂ i, ⋂ j, {P : Matrix (Fin n) (Fin n) ℝ | 0 ≤ P i j}) ∩
        (⋂ i, {P : Matrix (Fin n) (Fin n) ℝ | ∑ j, P i j = a i})) ∩
        (⋂ j, {P : Matrix (Fin n) (Fin n) ℝ | ∑ i, P i j = b j}) := by
      ext P
      simp [hU, CompOT.Assignment.couplings, Set.mem_iInter, and_assoc]
    rw [this]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le continuous_const (hcont i j)
    · exact isClosed_iInter fun i => isClosed_eq
        (continuous_finset_sum _ fun j _ => hcont i j) continuous_const
    · exact isClosed_iInter fun j => isClosed_eq
        (continuous_finset_sum _ fun i _ => hcont i j) continuous_const
  -- boundedness
  have hbox : IsCompact (Set.pi Set.univ fun i : Fin n =>
      Set.pi Set.univ fun j : Fin n => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  have hsub : U ⊆ (Set.pi Set.univ fun i : Fin n =>
      Set.pi Set.univ fun j : Fin n => Set.Icc (0 : ℝ) 1) := by
    intro P hP i _ j _
    refine ⟨hP.1 i j, ?_⟩
    have h1 : P i j ≤ ∑ j', P i j' :=
      Finset.single_le_sum (fun j' _ => hP.1 i j') (Finset.mem_univ j)
    rw [hP.2.1 i] at h1
    have : a i ≤ 1 := by
      have := Finset.single_le_sum (fun j' _ => ha.1 j') (Finset.mem_univ i)
      rw [ha.2] at this
      exact this
    linarith
  have hcomp : IsCompact U := hbox.of_isClosed_subset hclosed hsub
  have hne : U.Nonempty := by
    refine ⟨Matrix.of fun i j => a i * b j, fun i j => ?_, fun i => ?_, fun j => ?_⟩
    · exact mul_nonneg (ha.1 i) (hb.1 j)
    · simp [← Finset.mul_sum, hb.2]
    · simp [← Finset.sum_mul, ha.2]
  set C := powCost D p with hC
  have hfc : Continuous fun P : Matrix (Fin n) (Fin n) ℝ => CompOT.Assignment.frob C P := by
    unfold CompOT.Assignment.frob
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      continuous_const.mul (hcont i j)
  obtain ⟨P0, hP0, hmin⟩ := hcomp.exists_isMinOn hne hfc.continuousOn
  have hmin' : ∀ Q ∈ U, CompOT.Assignment.frob C P0 ≤ CompOT.Assignment.frob C Q :=
    fun Q hQ => hmin hQ
  -- off-diagonal mass
  obtain ⟨i, j, hij, hPij⟩ : ∃ i j, i ≠ j ∧ P0 i j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hab
    funext i
    obtain ⟨_, hr, hc⟩ := hP0
    have h1 : a i = P0 i i := by
      rw [← hr i]
      exact Finset.sum_eq_single i (fun j _ hj => hcon i j (Ne.symm hj)) (by simp)
    have h2 : b i = P0 i i := by
      rw [← hc i]
      exact Finset.sum_eq_single i (fun j _ hj => hcon j i hj) (by simp)
    exact h1.trans h2.symm
  have hPij' : 0 < P0 i j := lt_of_le_of_ne (hP0.1 i j) (Ne.symm hPij)
  have hDij : 0 < D i j := lt_of_le_of_ne (hD_nonneg i j) (fun h => hij ((hD_zero i j).1 h.symm))
  have hCij : 0 < C i j := Real.rpow_pos_of_pos hDij p
  have hfpos : 0 < CompOT.Assignment.frob C P0 := by
    unfold CompOT.Assignment.frob
    have hterm : ∀ i' j', 0 ≤ C i' j' * P0 i' j' := fun i' j' =>
      mul_nonneg (Real.rpow_nonneg (hD_nonneg i' j') p) (hP0.1 i' j')
    have h1 : ∑ j', C i j' * P0 i j' ≥ C i j * P0 i j :=
      Finset.single_le_sum (fun j' _ => hterm i j') (Finset.mem_univ j)
    have h2 : ∑ i', ∑ j', C i' j' * P0 i' j' ≥ ∑ j', C i j' * P0 i j' :=
      Finset.single_le_sum (f := fun i' => ∑ j', C i' j' * P0 i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => hterm i' j') (Finset.mem_univ i)
    have := mul_pos hCij hPij'
    linarith
  have hinf : (⨅ P : U, CompOT.Assignment.frob C (P : Matrix (Fin n) (Fin n) ℝ)) =
      CompOT.Assignment.frob C P0 := by
    apply le_antisymm
    · have hbdd : BddBelow (Set.range fun P : U =>
          CompOT.Assignment.frob C (P : Matrix (Fin n) (Fin n) ℝ)) :=
        ⟨CompOT.Assignment.frob C P0, by rintro _ ⟨Q, rfl⟩; exact hmin' Q.1 Q.2⟩
      exact ciInf_le hbdd ⟨P0, hP0⟩
    · haveI : Nonempty U := ⟨⟨P0, hP0⟩⟩
      exact le_ciInf fun Q => hmin' Q.1 Q.2
  unfold W otCost
  rw [hinf]
  exact Real.rpow_pos_of_pos hfpos _
