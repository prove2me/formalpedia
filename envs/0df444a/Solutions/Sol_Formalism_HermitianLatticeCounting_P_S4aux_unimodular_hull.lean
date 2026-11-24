-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.unimodular_hull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:02.938471+00:00
-- url     : https://prove2.me/submissions/ed45c398-4433-45a1-a091-bd89574d5ff0

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_dual_capacity_formula
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_mul_eq_zero_of_card_lt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_not_unit_of_mem_mO
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_polar_mO
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_gen
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_proj
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_li
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_span
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_extend_family
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_full_span
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : UnimodHull := by
  intro o O abelian₂ _ _ _ _ _ _ _ _ _ _ h hU hSD S m₀ hS hSfree hSrank
  classical
  have hH := hSD.1
  have : Nontrivial O := Module.nontrivial_of_finrank_pos (R := o) (by rw [hU.rank2]; norm_num)
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  have : IsNoetherianRing O := IsNoetherianRing.of_finite o O
  have : Module.Finite O S := inferInstance
  let P : ℕ → Prop := fun p => ∃ u : Fin p → abelian₂, (∀ i, ∀ s ∈ S, h (u i) s = 0) ∧
    (∀ i j, i ≠ j → h (u i) (u j) = 0) ∧ ∀ i, IsUnit (h (u i) (u i))
  have hP0 : P 0 := ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hPle : ∀ p, P p → p ≤ Module.finrank O abelian₂ := by
    rintro p ⟨u, _, huo, huu⟩
    have := (orth_li h u huo huu).fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  obtain ⟨p, hp, hmax⟩ : ∃ p, P p ∧ ¬ P (p + 1) := by
    refine ⟨Nat.findGreatest P (Module.finrank O abelian₂), Nat.findGreatest_spec (Nat.zero_le _) hP0, ?_⟩
    intro hq
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hPle _ hq) hq
  have hpn := hPle p hp
  obtain ⟨u, huS, huo, huu⟩ := hp
  let N' : Submodule O abelian₂ :=
    { carrier := {c | (∀ s ∈ S, h c s = 0) ∧ ∀ i, h c (u i) = 0}
      add_mem' := fun {a b} ha hb => ⟨fun s hs => by
          rw [map_add, LinearMap.add_apply, ha.1 s hs, hb.1 s hs, add_zero], fun i => by
          rw [map_add, LinearMap.add_apply, ha.2 i, hb.2 i, add_zero]⟩
      zero_mem' := ⟨fun s _ => by simp, fun i => by simp⟩
      smul_mem' := fun r c hc => ⟨fun s hs => by
          rw [map_smul, LinearMap.smul_apply, hc.1 s hs, smul_zero], fun i => by
          rw [map_smul, LinearMap.smul_apply, hc.2 i, smul_zero]⟩ }
  have hN' : ∀ c ∈ N', ¬ IsUnit (h c c) := by
    intro c hc hcu
    apply hmax
    refine ⟨Fin.cons c u, fun i => ?_, fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hc.1
      · simpa using huS i
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hne; exact absurd rfl hne
      · intro _; simpa using hc.2 j
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hH c (u i), hc.2 i, star_zero]
      · intro hne
        simp only [Fin.cons_succ]
        exact huo i j (fun e => hne (by rw [e]))
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hcu
      · simpa using huu i
  have hJ := polar_mO hU h hH N' hN'
  obtain ⟨r, hr⟩ : ∃ r, p + r = Module.finrank O abelian₂ := ⟨Module.finrank O abelian₂ - p, by omega⟩
  obtain ⟨t, htu, hto, htn⟩ := extend_family h hU hSD u huo huu r (by rw [Fintype.card_fin]; omega)
  have hut : ∀ i j, h (u i) (t j) = 0 := fun i j => by rw [hH (t j) (u i), htu, star_zero]
  have hfull : Submodule.span O (Set.range (Sum.elim u t)) = ⊤ := by
    apply full_span h
    · rintro (i | i) (j | j) hne
      · exact huo i j (fun e => hne (by rw [e]))
      · exact hut i j
      · exact htu i j
      · exact hto i j (fun e => hne (by rw [e]))
    · rintro (i | i); exacts [huu i, htn i]
    · rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hr]
  have hdec : ∀ x : abelian₂, ∃ (a : Fin p → O) (b : Fin r → O), x = ∑ i, a i • u i + ∑ j, b j • t j := by
    intro x
    have hx : x ∈ Submodule.span O (Set.range (Sum.elim u t)) := by rw [hfull]; trivial
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨fun i => cf (Sum.inl i), fun j => cf (Sum.inr j), ?_⟩
    rw [← hcf, Fintype.sum_sum_type]
    rfl
  have hmemT : ∀ b : Fin r → O, ∑ j, b j • t j ∈ Submodule.span O (Set.range t) := fun b =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmemU : ∀ a : Fin p → O, ∑ i, a i • u i ∈ Submodule.span O (Set.range u) := fun a =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨hT1, hT2, hT3, _⟩ := orth_span h t hto htn
  obtain ⟨hU1, hU2, _, hU4⟩ := orth_span h u huo huu
  rw [Fintype.card_fin] at hT2 hU2
  have hsu : ∀ s ∈ S, ∀ i, h s (u i) = 0 := fun s hs i => by rw [hH (u i) s, huS i s hs, star_zero]

  have hrank : r ≤ 2 * m₀ := by
    by_contra hlt
    push Not at hlt
    let bS := Module.Free.chooseBasis O S
    have hcardS : Fintype.card (Module.Free.ChooseBasisIndex O S) = m₀ := by
      rw [← hSrank, Module.finrank_eq_card_chooseBasisIndex]
    let sv : Module.Free.ChooseBasisIndex O S → abelian₂ := fun l => (bS l : abelian₂)
    have hsvS : ∀ l, sv l ∈ S := fun l => (bS l).2
    have hw0 : ∀ j, ∃ w, ∀ v : S, bS.coord j v = h v w := fun j =>
      dual_capacity_formula o O abelian₂ h hU hSD S hS (bS.coord j)
    choose w0 hw0 using hw0
    choose uu huu' using huu
    let w : Module.Free.ChooseBasisIndex O S → abelian₂ := fun j =>
      w0 j - ∑ i, (h (w0 j) (u i) * ((uu i)⁻¹ : Oˣ)) • u i
    have hwu : ∀ j i, h (w j) (u i) = 0 := fun j i => orth_proj h u huo uu huu' (w0 j) i
    have hsw : ∀ l j, h (sv l) (w j) = if l = j then 1 else 0 := by
      intro l j
      have e1 : h (sv l) (w j) = h (sv l) (w0 j) := by
        simp only [w]
        rw [map_sub, orth_pair_gen]
        rw [Finset.sum_eq_zero (fun i _ => by rw [hsu _ (hsvS l) i, mul_zero]), sub_zero]
      rw [e1, ← hw0 j (bS l), Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    have hws : ∀ j l, h (w j) (sv l) = if l = j then 1 else 0 := by
      intro j l
      rw [hH (sv l) (w j), hsw]; split_ifs <;> simp
    let c : Fin r → Module.Free.ChooseBasisIndex O S → O := fun i l => h (t i) (sv l)
    let nn : Fin r → abelian₂ := fun i => t i - ∑ l, c i l • w l
    have hnnsv : ∀ i l, h (nn i) (sv l) = 0 := by
      intro i l
      simp only [nn]
      rw [map_sub, LinearMap.sub_apply, orth_pair_left]
      simp only [hws, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp [c]
    have hnn : ∀ i, nn i ∈ N' := by
      intro i
      refine ⟨fun s hs => ?_, fun i' => ?_⟩
      · have es : s = ∑ l, bS.repr ⟨s, hs⟩ l • sv l := by
          have e0 : ((∑ l, bS.repr ⟨s, hs⟩ l • bS l : S) : abelian₂) = s :=
            congrArg Subtype.val (bS.sum_repr ⟨s, hs⟩)
          rw [Submodule.coe_sum] at e0
          exact e0.symm
        rw [es, orth_pair_gen]
        exact Finset.sum_eq_zero fun l _ => by rw [hnnsv, mul_zero]
      · simp only [nn]
        rw [map_sub, LinearMap.sub_apply, orth_pair_left, htu]
        rw [Finset.sum_eq_zero (fun l _ => by rw [hwu, mul_zero]), sub_zero]
    have hti : ∀ i, t i = ∑ l, c i l • w l + nn i := fun i => by simp [nn]
    have hD : ∀ i l, h (t i) (t l) = (∑ j, c i j * h (w j) (t l) + ∑ j, h (nn i) (w j) * star (c l j))
        + h (nn i) (nn l) := by
      intro i l
      have e1 : h (t i) (t l) = h (∑ j, c i j • w j) (t l) + h (nn i) (t l) := by
        conv_lhs => rw [hti i]
        rw [map_add, LinearMap.add_apply]
      have e2 : h (nn i) (t l) = h (nn i) (∑ j, c l j • w j) + h (nn i) (nn l) := by
        conv_lhs => rw [hti l]
        rw [map_add]
      rw [e1, e2, orth_pair_left, orth_pair_gen, ← add_assoc]
      congr 2
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hdetD : IsUnit (Matrix.of fun i l => h (t i) (t l)).det := by
      have : (Matrix.of fun i l => h (t i) (t l)) = Matrix.diagonal fun i => h (t i) (t i) := by
        ext i l
        rw [Matrix.diagonal_apply, Matrix.of_apply]
        split_ifs with hil
        · rw [hil]
        · exact hto i l hil
      rw [this, Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 htn
    apply not_unit_of_mem_mO hU _ _ hdetD
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_det]
    let A : Matrix (Fin r) (Module.Free.ChooseBasisIndex O S ⊕ Module.Free.ChooseBasisIndex O S) O :=
      Matrix.of fun i => Sum.elim (fun j => c i j) (fun j => h (nn i) (w j))
    let B : Matrix (Module.Free.ChooseBasisIndex O S ⊕ Module.Free.ChooseBasisIndex O S) (Fin r) O :=
      Matrix.of (Sum.elim (fun j l => h (w j) (t l)) (fun j l => star (c l j)))
    have hmap : (Ideal.Quotient.mk (mO o O)).mapMatrix (Matrix.of fun i l => h (t i) (t l))
        = (A.map (Ideal.Quotient.mk (mO o O))) * (B.map (Ideal.Quotient.mk (mO o O))) := by
      rw [← Matrix.map_mul]
      ext i l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, A, B,
        Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      rw [hD i l, map_add _ (_ + _), (Ideal.Quotient.eq_zero_iff_mem).2 (hJ _ (hnn i) _ (hnn l)),
        add_zero]
    rw [hmap]
    apply det_mul_eq_zero_of_card_lt
    rw [Fintype.card_sum, Fintype.card_fin, hcardS]
    omega
  refine ⟨Submodule.span O (Set.range t), ?_, hT1, by rw [hT2]; exact hrank, hT3, ?_,
    Submodule.span O (Set.range u), hU1, by rw [hT2, hU2]; omega, ?_, ?_, hU4⟩
  · intro s hs
    obtain ⟨a, b, hab⟩ := hdec s
    have ha : ∀ i, a i = 0 := by
      intro i
      have h1 := hsu s hs i
      rw [hab, map_add, LinearMap.add_apply, orth_pair_left, orth_pair_left,
        Finset.sum_eq_zero (fun j _ => by rw [htu, mul_zero] : ∀ j ∈ univ, b j * h (t j) (u i) = 0),
        add_zero, Finset.sum_eq_single i (fun i' _ hi => by rw [huo i' i hi, mul_zero])
          (fun hi => absurd (Finset.mem_univ _) hi)] at h1
      exact (huu i).mul_left_eq_zero.1 h1
    rw [hab]
    simp only [ha, zero_smul, Finset.sum_const_zero, zero_add]
    exact hmemT b
  · intro x hx hx0
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    have hb : ∀ j, b j = 0 := by
      intro j
      have h1 := hx0 (t j) (Submodule.subset_span ⟨j, rfl⟩)
      rw [orth_pair_left, Finset.sum_eq_single j (fun i' _ hi => by rw [hto i' j hi, mul_zero])
          (fun hi => absurd (Finset.mem_univ _) hi)] at h1
      exact (htn j).mul_left_eq_zero.1 h1
    simp [hb]
  · intro x hx y hy
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hy
    rw [orth_pair_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [orth_pair_gen, Finset.sum_eq_zero (fun i _ => by rw [htu, mul_zero]), mul_zero]
  · intro x
    obtain ⟨a, b, hab⟩ := hdec x
    exact ⟨_, hmemT b, _, hmemU a, by rw [hab, add_comm]⟩
end Formalism.HermitianLatticeCounting.P.S4aux
