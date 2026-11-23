-- Prove2me | solution 1 for CorrelatedAuctionComplexity.Main.sum_gadget_correct
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T05:45:41.850134+00:00
-- url     : https://prove2.me/submissions/3ab2f4c6-e5a4-48ca-8c5e-cf6e9c839f30

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools
import Theorems.Thm_CorrelatedAuctionComplexity_Main_binary_deviation_inequalities
import Theorems.Thm_CorrelatedAuctionComplexity_Main_singleton_payoff_difference
import Theorems.Thm_CorrelatedAuctionComplexity_Main_anchored_payoff_difference

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open CorrelatedAuctionComplexity.Main

private lemma binaryEdgePure_zero {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (p : N → ℝ) (e : Fin H.edges.length) (i : N) (t : Bool)
    (hi : i ∉ (H.edge e).participants) :
    H.binaryEdgePure p e i t = 0 := by
  simp [HDFPA.binaryEdgePure, expectation, AGT.profileProb, singlePayoff, hi]

private lemma delta_zero {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (p : N → ℝ) (e : Fin H.edges.length) (i : N)
    (hi : i ∉ (H.edge e).participants) :
    H.delta p {e} i = 0 := by
  simp [HDFPA.delta, binaryEdgePure_zero H p e i _ hi]

private lemma totalDelta_eq_gadget_of_auxiliary {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (G : Gadget N)
    (ids : Fin G.auctions.length → Fin H.edges.length)
    (hocc : Occurs H G ids 1) (a : N) (ha : a ∈ G.auxiliaries) (p : N → ℝ) :
    H.totalDelta p a = H.delta p (gadgetEdges H G ids) a := by
  classical
  unfold HDFPA.totalDelta
  symm
  unfold HDFPA.delta
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e he heR
  have herange : e ∉ Set.range ids := by
    intro her
    obtain ⟨j, rfl⟩ := her
    apply heR
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hnot := hocc.2.2 e herange a ha
  simp [binaryEdgePure_zero H p e a _ hnot]

private lemma incidentWeight_eq_gadget_of_auxiliary {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (G : Gadget N)
    (ids : Fin G.auctions.length → Fin H.edges.length)
    (hocc : Occurs H G ids 1) (a : N) (ha : a ∈ G.auxiliaries) :
    H.incidentWeight a = ∑ e ∈ gadgetEdges H G ids,
      if a ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0 := by
  classical
  unfold HDFPA.incidentWeight
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e he heR
  have herange : e ∉ Set.range ids := by
    intro her
    obtain ⟨j, rfl⟩ := her
    apply heR
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hnot := hocc.2.2 e herange a ha
  simp [hnot]

private lemma pair_delta {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (x y : N) (hxy : x ≠ y)
    (hx : H.value x ∈ ({2,3,4} : Finset ℚ))
    (hy : H.value y ∈ ({2,3,4} : Finset ℚ))
    (e : Fin H.edges.length) (he : (H.edge e).participants = {x,y})
    (p : N → ℝ) (hp : H.LegalBinary p) :
    H.delta p {e} x = ((H.edge e).weight : ℝ) *
      (((H.value x : ℝ)/2 - ((H.value x : ℝ)-1)/2) * p y +
        (H.value x : ℝ)-1-(H.value x : ℝ)/2) := by
  have hfresh : ∀ j : Fin 0, Fin.elim0 j ≠ x ∧ Fin.elim0 j ≠ y := by
    intro j
    exact Fin.elim0 j
  have hvz : ∀ j : Fin 0, H.value (Fin.elim0 j) = 1/2 := by
    intro j
    exact Fin.elim0 j
  have hh := anchored_payoff_difference H hH hB 0 x y hxy (Fin.elim0 : Fin 0 → N)
    (by simp) hfresh hx hy hvz e (by simpa using he) p hp
  norm_num at hh ⊢
  exact hh

private lemma two_anchor_delta {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (x y a b : N) (hxy : x ≠ y) (hab : a ≠ b)
    (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x) (hby : b ≠ y)
    (hx : H.value x ∈ ({2,3,4} : Finset ℚ))
    (hy : H.value y ∈ ({2,3,4} : Finset ℚ))
    (hva : H.value a = 1/2) (hvb : H.value b = 1/2)
    (e : Fin H.edges.length) (he : (H.edge e).participants = {x,y,a,b})
    (p : N → ℝ) (hp : H.LegalBinary p) :
    H.delta p {e} x = ((H.edge e).weight : ℝ) *
      (((H.value x : ℝ)/4 - ((H.value x : ℝ)-1)/2) * p y +
        (H.value x : ℝ)-1-(H.value x : ℝ)/4) := by
  let z : Fin 2 → N := ![a,b]
  have hzi : Function.Injective z := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [z]
  have hz : (List.ofFn z).Nodup := List.nodup_ofFn.mpr hzi
  have hfresh : ∀ j, z j ≠ x ∧ z j ≠ y := by
    intro j
    fin_cases j <;> simp [z, hax, hay, hbx, hby]
  have hvz : ∀ j, H.value (z j) = 1/2 := by
    intro j
    fin_cases j <;> simp [z, hva, hvb]
  have himage : Finset.univ.image z = {a,b} := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j <;> simp [z]
    · intro hk
      rcases hk with rfl | rfl
      · exact ⟨0, by simp [z]⟩
      · exact ⟨1, by simp [z]⟩
  have he' : (H.edge e).participants = {x,y} ∪ Finset.univ.image z := by
    rw [he, himage]
    ext k
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hh := anchored_payoff_difference H hH hB 2 x y hxy z hz hfresh hx hy hvz e he' p hp
  norm_num at hh ⊢
  exact hh

private lemma delta_gadget_sum {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (p : N → ℝ) (G : Gadget N)
    (ids : Fin G.auctions.length → Fin H.edges.length) (hinj : Function.Injective ids)
    (i : N) :
    H.delta p (gadgetEdges H G ids) i = ∑ j, H.delta p {ids j} i := by
  classical
  unfold HDFPA.delta gadgetEdges
  rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
  apply Finset.sum_congr rfl
  intro j hj
  simp

 theorem solution {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (x₁ x₂ y h : N) (z : Fin 6 → N) (hroles : SumRoles H x₁ x₂ y h z)
    (ids : Fin (sumGadget x₁ x₂ y h z).auctions.length → Fin H.edges.length)
    (hocc : Occurs H (sumGadget x₁ x₂ y h z) ids 1)
    (houtput : ∀ q : N → ℝ, H.LegalBinary q →
      H.totalDelta q y = H.delta q (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) y)
    (Γ : ℝ) (hΓ : H.incidentWeight y ≤ Γ)
    (p : N → ℝ) (hp : H.LegalBinary p) (η : ℝ) (hη : 0 ≤ η) :
    H.delta p (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) h = p y-p x₁-p x₂ ∧
      H.delta p (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) y = 1-2*p h ∧
      (H.IsNE η (H.binaryProfile p) → |p y-min (p x₁+p x₂) 1| ≤ max 300 (2*Γ)*η) := by
  classical
  change (Fin 6 → Fin H.edges.length) at ids
  change Occurs H (sumGadget x₁ x₂ y h z) ids 1 at hocc
  have hlen : (sumGadget x₁ x₂ y h z).auctions.length = 6 := by rfl
  have hed (j : Fin 6) := hocc.2.1 (Fin.cast hlen.symm j)
  rcases hroles with ⟨hnodup, hfresh, hx1, hx2, hy, hh, hz⟩
  have hnodup' := (List.nodup_cons.mp hnodup).2
  have hny : y ∉ h :: List.ofFn z := (List.nodup_cons.mp hnodup).1
  have hnh : h ∉ List.ofFn z := (List.nodup_cons.mp hnodup').1
  have hznodup : (List.ofFn z).Nodup := (List.nodup_cons.mp hnodup').2
  have hzi : Function.Injective z := List.nodup_ofFn.mp hznodup
  have hzne {i j : Fin 6} (hij : i ≠ j) : z i ≠ z j := fun hzz => hij (hzi hzz)
  have hyh : y ≠ h := by
    intro eyh
    apply hny
    simp [eyh]
  have hyz (j : Fin 6) : y ≠ z j := by
    intro eyz
    apply hny
    apply List.mem_cons.mpr
    exact Or.inr (List.mem_ofFn.mpr ⟨j, eyz.symm⟩)
  have hhz (j : Fin 6) : h ≠ z j := by
    intro ehz
    apply hnh
    exact List.mem_ofFn.mpr ⟨j, ehz.symm⟩
  have hyx1 : y ≠ x₁ := (hfresh y (by simp)).1
  have hyx2 : y ≠ x₂ := (hfresh y (by simp)).2
  have hhx1 : h ≠ x₁ := (hfresh h (by simp)).1
  have hhx2 : h ≠ x₂ := (hfresh h (by simp)).2
  have hzx (j : Fin 6) : z j ≠ x₁ ∧ z j ≠ x₂ := by
    apply hfresh
    apply List.mem_cons.mpr
    apply Or.inr
    apply List.mem_cons.mpr
    exact Or.inr (List.mem_ofFn.mpr ⟨j, rfl⟩)
  have hxv1 : H.value x₁ ∈ ({2,3,4} : Finset ℚ) := by simp [hx1]
  have hxv2 : H.value x₂ ∈ ({2,3,4} : Finset ℚ) := by simp [hx2]
  have hyv : H.value y ∈ ({2,3,4} : Finset ℚ) := by simp [hy]
  have hhv : H.value h ∈ ({2,3,4} : Finset ℚ) := by simp [hh]
  have he0 : (H.edge (ids 0)).participants = {x₁,h,z 0,z 1} := by
    simpa [sumGadget] using (hed 0).1
  have he1 : (H.edge (ids 1)).participants = {x₂,h,z 2,z 3} := by
    simpa [sumGadget] using (hed 1).1
  have he2 : (H.edge (ids 2)).participants = {y,h} := by
    simpa [sumGadget] using (hed 2).1
  have he3 : (H.edge (ids 3)).participants = {y,h,z 4,z 5} := by
    simpa [sumGadget] using (hed 3).1
  have he4 : (H.edge (ids 4)).participants = {h} := by
    simpa [sumGadget] using (hed 4).1
  have he5 : (H.edge (ids 5)).participants = {y} := by
    simpa [sumGadget] using (hed 5).1
  have hw0 : ((H.edge (ids 0)).weight : ℝ) = 4 := by
    simpa [sumGadget] using (hed 0).2
  have hw1 : ((H.edge (ids 1)).weight : ℝ) = 4 := by
    simpa [sumGadget] using (hed 1).2
  have hw2 : ((H.edge (ids 2)).weight : ℝ) = 8 := by
    simpa [sumGadget] using (hed 2).2
  have hw3 : ((H.edge (ids 3)).weight : ℝ) = 12 := by
    simpa [sumGadget] using (hed 3).2
  have hw4 : ((H.edge (ids 4)).weight : ℝ) = 29 := by
    simpa [sumGadget] using (hed 4).2
  have hw5 : ((H.edge (ids 5)).weight : ℝ) = 31 := by
    simpa [sumGadget] using (hed 5).2
  have hsum (i : N) :
      H.delta p (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) i =
        ∑ j, H.delta p {ids j} i :=
    delta_gadget_sum H p (sumGadget x₁ x₂ y h z) ids hocc.1 i
  have hd0h : H.delta p {ids 0} h = 4*(5/4-p x₁/4) := by
    rw [two_anchor_delta H hH hB h x₁ (z 0) (z 1) hhx1
      (hzne (by decide)) (hhz 0).symm (hzx 0).1
      (hhz 1).symm (hzx 1).1 hhv hxv1 (hz 0) (hz 1) (ids 0)
      (by simpa [Finset.insert_comm] using he0) p hp]
    rw [hw0, hh]
    ring
  have hd1h : H.delta p {ids 1} h = 4*(5/4-p x₂/4) := by
    rw [two_anchor_delta H hH hB h x₂ (z 2) (z 3) hhx2
      (hzne (by decide)) (hhz 2).symm (hzx 2).2
      (hhz 3).symm (hzx 3).2 hhv hxv2 (hz 2) (hz 3) (ids 1)
      (by simpa [Finset.insert_comm] using he1) p hp]
    rw [hw1, hh]
    ring
  have hd2h : H.delta p {ids 2} h = 8*(1/2+p y/2) := by
    rw [pair_delta H hH hB h y hyh.symm hhv hyv (ids 2)
      (by simpa [Finset.pair_comm] using he2) p hp]
    rw [hw2, hh]
    ring
  have hd3h : H.delta p {ids 3} h = 12*(5/4-p y/4) := by
    rw [two_anchor_delta H hH hB h y (z 4) (z 5) hyh.symm
      (hzne (by decide)) (hhz 4).symm (hyz 4).symm
      (hhz 5).symm (hyz 5).symm hhv hyv (hz 4) (hz 5) (ids 3)
      (by simpa [Finset.insert_comm] using he3) p hp]
    rw [hw3, hh]
    ring
  have hd4h : H.delta p {ids 4} h = -29 := by
    rw [singleton_payoff_difference H hH hB h hhv (ids 4) he4 p hp, hw4]
  have hd5h : H.delta p {ids 5} h = 0 := by
    apply delta_zero
    simp [he5, hyh.symm]
  have hdh : H.delta p (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) h =
      p y-p x₁-p x₂ := by
    rw [hsum h]
    change (∑ j : Fin 6, H.delta p {ids j} h) = _
    rw [Fin.sum_univ_six, hd0h, hd1h, hd2h, hd3h, hd4h, hd5h]
    ring
  have hd0y : H.delta p {ids 0} y = 0 := by
    apply delta_zero
    simp [he0, hyx1, hyh, hyz]
  have hd1y : H.delta p {ids 1} y = 0 := by
    apply delta_zero
    simp [he1, hyx2, hyh, hyz]
  have hd2y : H.delta p {ids 2} y = 8*(1+p h/2) := by
    rw [pair_delta H hH hB y h hyh hyv hhv (ids 2) he2 p hp]
    rw [hw2, hy]
    ring
  have hd3y : H.delta p {ids 3} y = 12*(2-p h/2) := by
    rw [two_anchor_delta H hH hB y h (z 4) (z 5) hyh
      (hzne (by decide)) (hyz 4).symm (hhz 4).symm
      (hyz 5).symm (hhz 5).symm hyv hhv (hz 4) (hz 5) (ids 3) he3 p hp]
    rw [hw3, hy]
    ring
  have hd4y : H.delta p {ids 4} y = 0 := by
    apply delta_zero
    simp [he4, hyh]
  have hd5y : H.delta p {ids 5} y = -31 := by
    rw [singleton_payoff_difference H hH hB y hyv (ids 5) he5 p hp, hw5]
  have hdy : H.delta p (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) y = 1-2*p h := by
    rw [hsum y]
    change (∑ j : Fin 6, H.delta p {ids j} y) = _
    rw [Fin.sum_univ_six, hd0y, hd1y, hd2y, hd3y, hd4y, hd5y]
    ring
  refine ⟨hdh, hdy, ?_⟩
  intro hne
  have hdev := binary_deviation_inequalities H hH hB η hη p hne
  have htotal : H.totalDelta p h =
      H.delta p (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) h :=
    totalDelta_eq_gadget_of_auxiliary H (sumGadget x₁ x₂ y h z) ids hocc h
      (by simp [sumGadget]) p
  have hOccW : H.incidentWeight h = ∑ e ∈ gadgetEdges H (sumGadget x₁ x₂ y h z) ids,
      if h ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0 :=
    incidentWeight_eq_gadget_of_auxiliary H (sumGadget x₁ x₂ y h z) ids hocc h
      (by simp [sumGadget])
  have hW : H.incidentWeight h = 57 := by
    rw [hOccW]
    dsimp [gadgetEdges]
    rw [Finset.sum_image (fun a _ b _ hab => hocc.1 hab)]
    change (∑ j : Fin 6, if h ∈ (H.edge (ids j)).participants then
      ((H.edge (ids j)).weight : ℝ) else 0) = 57
    rw [Fin.sum_univ_six, he0, he1, he2, he3, he4, he5,
      hw0, hw1, hw2, hw3, hw4, hw5]
    simp [hyh, hyh.symm]
    norm_num
  have hWnonneg (i : N) : 0 ≤ H.incidentWeight i := by
    unfold HDFPA.incidentWeight
    apply Finset.sum_nonneg
    intro e he
    split_ifs
    · exact_mod_cast (hH.2.2.2.2.1 (H.edge e) (List.getElem_mem _)).2.le
    · exact le_rfl
  have hΓ0 : 0 ≤ Γ := (hWnonneg y).trans hΓ
  have hM300 : (300 : ℝ) ≤ max 300 (2*Γ) := le_max_left _ _
  have hMΓ : 2*Γ ≤ max 300 (2*Γ) := le_max_right _ _
  have hM0 : 0 ≤ max 300 (2*Γ) := by linarith
  have hMη0 : 0 ≤ max 300 (2*Γ)*η := mul_nonneg hM0 hη
  have hmin0 : 0 ≤ min (p x₁+p x₂) 1 :=
    le_min (add_nonneg (hp.1 x₁).1 (hp.1 x₂).1) zero_le_one
  apply abs_le.mpr
  constructor
  · by_contra! hbad
    have hdneg : H.totalDelta p h < 0 := by
      rw [htotal, hdh]
      have hm := min_le_left (p x₁+p x₂) 1
      have h300 := mul_le_mul_of_nonneg_right hM300 hη
      linarith
    have hhin := (hdev h).2 hdneg
    rw [htotal, hdh, hW] at hhin
    have hD : p y-p x₁-p x₂ < -300*η := by
      have hm := min_le_left (p x₁+p x₂) 1
      have h300 := mul_le_mul_of_nonneg_right hM300 hη
      linarith
    have hph : p h < 1/5 := by
      by_contra! hph
      have hmul := mul_le_mul_of_nonneg_left hph
        (show 0 ≤ -(p y-p x₁-p x₂) by linarith)
      nlinarith only [hη, hhin, hD, hmul]
    have hdypos : 0 < H.totalDelta p y := by
      rw [houtput p hp, hdy]
      linarith
    have hyin := (hdev y).1 hdypos
    rw [houtput p hp, hdy] at hyin
    have hyweight : η*H.incidentWeight y ≤ η*Γ := mul_le_mul_of_nonneg_left hΓ hη
    have hmuly : (3/5)*(1-p y) ≤ (1-p y)*(1-2*p h) := by
      have hcoef : (3/5 : ℝ) ≤ 1-2*p h := by linarith
      have hy0 : 0 ≤ 1-p y := sub_nonneg.mpr (hp.1 y).2
      have hm := mul_le_mul_of_nonneg_right hcoef hy0
      nlinarith only [hm]
    have hchain : (3/5)*(1-p y) ≤ η*Γ := hmuly.trans (hyin.trans hyweight)
    have hybound : 1-p y ≤ max 300 (2*Γ)*η := by
      have h2 := mul_le_mul_of_nonneg_right hMΓ hη
      nlinarith only [hchain, h2, mul_nonneg hΓ0 hη]
    have hm := min_le_right (p x₁+p x₂) 1
    linarith
  · by_contra! hbad
    have hs : p x₁+p x₂ ≤ 1 := by
      by_contra! hs
      have hs' : 1 ≤ p x₁+p x₂ := hs.le
      rw [min_eq_right hs'] at hbad
      linarith [(hp.1 y).2]
    rw [min_eq_left hs] at hbad
    have hdpos : 0 < H.totalDelta p h := by
      rw [htotal, hdh]
      have h300 := mul_le_mul_of_nonneg_right hM300 hη
      linarith
    have hhin := (hdev h).1 hdpos
    rw [htotal, hdh, hW] at hhin
    have hD : 300*η < p y-p x₁-p x₂ := by
      have h300 := mul_le_mul_of_nonneg_right hM300 hη
      linarith
    have hph : 4/5 < p h := by
      by_contra! hph
      have hmul := mul_le_mul_of_nonneg_right
        (show (1/5 : ℝ) ≤ 1-p h by linarith) (show 0 ≤ p y-p x₁-p x₂ by linarith)
      nlinarith only [hη, hhin, hD, hmul]
    have hdyneg : H.totalDelta p y < 0 := by
      rw [houtput p hp, hdy]
      linarith
    have hyin := (hdev y).2 hdyneg
    rw [houtput p hp, hdy] at hyin
    have hyweight : η*H.incidentWeight y ≤ η*Γ := mul_le_mul_of_nonneg_left hΓ hη
    have hmuly : (3/5)*p y ≤ -(p y)*(1-2*p h) := by
      have hcoef : (3/5 : ℝ) ≤ 2*p h-1 := by linarith
      have hm := mul_le_mul_of_nonneg_left hcoef (hp.1 y).1
      nlinarith only [hm]
    have hchain : (3/5)*p y ≤ η*Γ := hmuly.trans (hyin.trans hyweight)
    have hybound : p y ≤ max 300 (2*Γ)*η := by
      have h2 := mul_le_mul_of_nonneg_right hMΓ hη
      nlinarith only [hchain, h2, mul_nonneg hΓ0 hη]
    linarith [(hp.1 x₁).1, (hp.1 x₂).1]