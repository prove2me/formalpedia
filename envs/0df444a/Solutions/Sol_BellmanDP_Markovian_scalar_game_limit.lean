-- Prove2me | solution 1 for BellmanDP.Markovian.scalar_game_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:53:07.092161+00:00
-- url     : https://prove2.me/submissions/e675ea3c-b4a2-4dba-8ea5-e684b92ab4d8

import Mathlib
import Definitions.Def_BellmanDP_Markovian_ScalarGame



namespace BellmanDP.Markovian

open Filter Topology

lemma sg_pair_add_q {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin n → ℝ) (q1 q2 : Fin m → ℝ)
    (a b : ℝ) : pairing A p (a • q1 + b • q2) = a * pairing A p q1 + b * pairing A p q2 := by
  simp [pairing, add_dotProduct, smul_dotProduct]

lemma sg_pair_add_p {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p1 p2 : Fin n → ℝ) (q : Fin m → ℝ)
    (a b : ℝ) : pairing A (a • p1 + b • p2) q = a * pairing A p1 q + b * pairing A p2 q := by
  simp [pairing, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul]

lemma sg_pair_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin n → ℝ) (q : Fin m → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (hq : q ∈ stdSimplex ℝ (Fin m)) :
    |pairing A p q| ≤ ∑ i, ∑ j, |A i j| := by
  have hp1 : ∀ j, p j ≤ 1 := fun j => by
    rw [← hp.2]; exact Finset.single_le_sum (fun k _ => hp.1 k) (Finset.mem_univ j)
  have hq1 : ∀ i, q i ≤ 1 := fun i => by
    rw [← hq.2]; exact Finset.single_le_sum (fun k _ => hq.1 k) (Finset.mem_univ i)
  simp only [pairing, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (hq.1 i)]
  have h1 : |A i j * p j| ≤ |A i j| := by
    rw [abs_mul, abs_of_nonneg (hp.1 j)]
    exact mul_le_of_le_one_right (abs_nonneg _) (hp1 j)
  rw [← abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (hq1 i)).trans h1

lemma sg_pair_cont_q {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin n → ℝ) :
    Continuous fun q : Fin m → ℝ => pairing A p q := by
  simp only [pairing, dotProduct]; fun_prop

lemma sg_pair_cont_p {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (q : Fin m → ℝ) :
    Continuous fun p : Fin n → ℝ => pairing A p q := by
  simp only [pairing, dotProduct, Matrix.mulVec]; fun_prop

lemma sg_inf_pert {ι : Type*} (s : Set ι) (hs : s.Nonempty) (φ ψ : ι → ℝ) (K L : ℝ)
    (hφ : ∀ x ∈ s, -K ≤ φ x) (h : ∀ x ∈ s, φ x ≤ ψ x + L) :
    sInf (φ '' s) ≤ sInf (ψ '' s) + L := by
  have hb : BddBelow (φ '' s) := ⟨-K, by rintro _ ⟨x, hx, rfl⟩; exact hφ x hx⟩
  have : sInf (φ '' s) - L ≤ sInf (ψ '' s) := by
    refine le_csInf (hs.image ψ) ?_
    rintro _ ⟨x, hx, rfl⟩
    have := csInf_le hb ⟨x, hx, rfl⟩
    linarith [h x hx]
  linarith

lemma sg_sup_pert {ι : Type*} (s : Set ι) (hs : s.Nonempty) (φ ψ : ι → ℝ) (K L : ℝ)
    (hψ : ∀ x ∈ s, ψ x ≤ K) (h : ∀ x ∈ s, φ x ≤ ψ x + L) :
    sSup (φ '' s) ≤ sSup (ψ '' s) + L := by
  have hb : BddAbove (ψ '' s) := ⟨K, by rintro _ ⟨x, hx, rfl⟩; exact hψ x hx⟩
  refine csSup_le (hs.image φ) ?_
  rintro _ ⟨x, hx, rfl⟩
  have := le_csSup hb ⟨x, hx, rfl⟩
  linarith [h x hx]

/-- the game facts: value v, sign conditions for gameRHS, Lipschitz. -/
lemma sg_game {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B : Matrix (Fin m) (Fin n) ℝ) (d : ℝ) (hd : 0 < d)
    (hB : ∀ p ∈ stdSimplex ℝ (Fin n), ∀ q ∈ stdSimplex ℝ (Fin m), d ≤ pairing B p q) :
    maxMinRatio A B = minMaxRatio A B ∧
      (∀ u, maxMinRatio A B ≤ u → gameRHS A B u ≤ d * (maxMinRatio A B - u)) ∧
      (∀ u, u ≤ maxMinRatio A B → d * (maxMinRatio A B - u) ≤ gameRHS A B u) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ u u', gameRHS A B u ≤ gameRHS A B u' + L * |u - u'| := by
  classical
  set X := stdSimplex ℝ (Fin n) with hX
  set Y := stdSimplex ℝ (Fin m) with hY
  have neX : X.Nonempty := ⟨Pi.single ⟨0, hn⟩ 1, single_mem_stdSimplex ℝ _⟩
  have neY : Y.Nonempty := ⟨Pi.single ⟨0, hm⟩ 1, single_mem_stdSimplex ℝ _⟩
  set KA := ∑ i, ∑ j, |A i j|
  set KB := ∑ i, ∑ j, |B i j|
  have hBpos : ∀ p ∈ X, ∀ q ∈ Y, 0 < pairing B p q := fun p hp q hq =>
    lt_of_lt_of_le hd (hB p hp q hq)
  let R : (Fin m → ℝ) → (Fin n → ℝ) → ℝ := fun q p => pairing A p q / pairing B p q
  have hRb : ∀ p ∈ X, ∀ q ∈ Y, |R q p| ≤ KA / d := by
    intro p hp q hq
    simp only [R]
    rw [abs_div, abs_of_pos (hBpos p hp q hq)]
    rw [div_le_div_iff₀ (hBpos p hp q hq) hd]
    have h1 := sg_pair_bound A p q hp hq
    have h2 := hB p hp q hq
    have h3 : 0 ≤ KA := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    nlinarith [abs_nonneg (pairing A p q)]
  -- Sion
  have hfy : ∀ p ∈ X, LowerSemicontinuousOn (fun q => R q p) Y := by
    intro p hp
    refine ContinuousOn.lowerSemicontinuousOn ?_
    exact ((sg_pair_cont_q A p).continuousOn).div ((sg_pair_cont_q B p).continuousOn)
      fun q hq => (hBpos p hp q hq).ne'
  have hfx : ∀ q ∈ Y, UpperSemicontinuousOn (fun p => R q p) X := by
    intro q hq
    refine ContinuousOn.upperSemicontinuousOn ?_
    exact ((sg_pair_cont_p A q).continuousOn).div ((sg_pair_cont_p B q).continuousOn)
      fun p hp => (hBpos p hp q hq).ne'
  have hfy' : ∀ p ∈ X, QuasiconvexOn ℝ Y (fun q => R q p) := by
    intro p hp r
    intro q1 hq1 q2 hq2 a b ha hb hab
    obtain ⟨hq1Y, hq1r⟩ := hq1
    obtain ⟨hq2Y, hq2r⟩ := hq2
    have hY' : a • q1 + b • q2 ∈ Y := convex_stdSimplex ℝ _ hq1Y hq2Y ha hb hab
    refine ⟨hY', ?_⟩
    simp only [R] at hq1r hq2r ⊢
    rw [div_le_iff₀ (hBpos p hp q1 hq1Y)] at hq1r
    rw [div_le_iff₀ (hBpos p hp q2 hq2Y)] at hq2r
    rw [div_le_iff₀ (hBpos p hp _ hY'), sg_pair_add_q, sg_pair_add_q]
    nlinarith
  have hfx' : ∀ q ∈ Y, QuasiconcaveOn ℝ X (fun p => R q p) := by
    intro q hq r
    intro p1 hp1 p2 hp2 a b ha hb hab
    obtain ⟨hp1X, hp1r⟩ := hp1
    obtain ⟨hp2X, hp2r⟩ := hp2
    have hX' : a • p1 + b • p2 ∈ X := convex_stdSimplex ℝ _ hp1X hp2X ha hb hab
    refine ⟨hX', ?_⟩
    simp only [R] at hp1r hp2r ⊢
    rw [le_div_iff₀ (hBpos p1 hp1X q hq)] at hp1r
    rw [le_div_iff₀ (hBpos p2 hp2X q hq)] at hp2r
    rw [le_div_iff₀ (hBpos _ hX' q hq), sg_pair_add_p, sg_pair_add_p]
    nlinarith
  obtain ⟨qs, hqs, ps, hps, hsad⟩ := Sion.exists_isSaddlePointOn neY (convex_stdSimplex ℝ _)
    (isCompact_stdSimplex ℝ _) hfy hfy' (convex_stdSimplex ℝ _) neX (isCompact_stdSimplex ℝ _)
    hfx hfx'
  -- hsad : ∀ q ∈ Y, ∀ p ∈ X, R qs p ≤ R q ps
  set v := R qs ps with hv
  have hsad1 : ∀ p ∈ X, R qs p ≤ v := fun p hp => hsad qs hqs p hp
  have hsad2 : ∀ q ∈ Y, v ≤ R q ps := fun q hq => hsad q hq ps hps
  have hmaxmin : maxMinRatio A B = v := by
    have hinner : ∀ p ∈ X, sInf ((fun q => pairing A p q / pairing B p q) '' Y) ≤ v := by
      intro p hp
      have hbb : BddBelow ((fun q => pairing A p q / pairing B p q) '' Y) := by
        refine ⟨-(KA / d), ?_⟩
        rintro _ ⟨q, hq, rfl⟩
        exact (abs_le.1 (hRb p hp q hq)).1
      exact (csInf_le hbb ⟨qs, hqs, rfl⟩).trans (hsad1 p hp)
    have hps' : sInf ((fun q => pairing A ps q / pairing B ps q) '' Y) = v := by
      refine IsLeast.csInf_eq ⟨⟨qs, hqs, rfl⟩, ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      exact hsad2 q hq
    refine IsGreatest.csSup_eq ⟨⟨ps, hps, hps'⟩, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact hinner p hp
  have hminmax : minMaxRatio A B = v := by
    have hinner : ∀ q ∈ Y, v ≤ sSup ((fun p => pairing A p q / pairing B p q) '' X) := by
      intro q hq
      have hbb : BddAbove ((fun p => pairing A p q / pairing B p q) '' X) := by
        refine ⟨KA / d, ?_⟩
        rintro _ ⟨p, hp, rfl⟩
        exact (abs_le.1 (hRb p hp q hq)).2
      exact (hsad2 q hq).trans (le_csSup hbb ⟨ps, hps, rfl⟩)
    have hqs' : sSup ((fun p => pairing A p qs / pairing B p qs) '' X) = v := by
      refine IsGreatest.csSup_eq ⟨⟨ps, hps, rfl⟩, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact hsad1 p hp
    refine IsLeast.csInf_eq ⟨⟨qs, hqs, hqs'⟩, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact hinner q hq
  -- payoff bounds
  let h : ℝ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ := fun u p q => pairing A p q - pairing B p q * u
  have hbd : ∀ u, ∀ p ∈ X, ∀ q ∈ Y, |h u p q| ≤ KA + KB * |u| := by
    intro u p hp q hq
    simp only [h]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    exact add_le_add (sg_pair_bound A p q hp hq)
      (mul_le_mul_of_nonneg_right (sg_pair_bound B p q hp hq) (abs_nonneg _))
  let Ψ : ℝ → (Fin n → ℝ) → ℝ := fun u p => sInf ((fun q => h u p q) '' Y)
  have hg : ∀ u, gameRHS A B u = sSup ((fun p => Ψ u p) '' X) := fun u => rfl
  have hΨlo : ∀ u, ∀ p ∈ X, -(KA + KB * |u|) ≤ Ψ u p := by
    intro u p hp
    refine le_csInf (neY.image _) ?_
    rintro _ ⟨q, hq, rfl⟩
    exact (abs_le.1 (hbd u p hp q hq)).1
  have hΨhi : ∀ u, ∀ p ∈ X, Ψ u p ≤ KA + KB * |u| := by
    intro u p hp
    obtain ⟨q0, hq0⟩ := neY
    have hbb : BddBelow ((fun q => h u p q) '' Y) := by
      refine ⟨-(KA + KB * |u|), ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      exact (abs_le.1 (hbd u p hp q hq)).1
    exact (csInf_le hbb ⟨q0, hq0, rfl⟩).trans (abs_le.1 (hbd u p hp q0 hq0)).2
  have hΨle : ∀ u, ∀ p ∈ X, ∀ q ∈ Y, Ψ u p ≤ h u p q := by
    intro u p hp q hq
    refine csInf_le ⟨-(KA + KB * |u|), ?_⟩ ⟨q, hq, rfl⟩
    rintro _ ⟨q', hq', rfl⟩
    exact (abs_le.1 (hbd u p hp q' hq')).1
  have hKB : 0 ≤ KB := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨hmaxmin.trans hminmax.symm, ?_, ?_, ⟨KB, hKB, ?_⟩⟩
  · intro u hu
    rw [hmaxmin] at hu ⊢
    rw [hg]
    refine csSup_le (neX.image _) ?_
    rintro _ ⟨p, hp, rfl⟩
    refine (hΨle u p hp qs hqs).trans ?_
    have e : h u p qs = pairing B p qs * (R qs p - u) := by
      simp only [h, R]; field_simp [(hBpos p hp qs hqs).ne']
    rw [e]
    have h1 := hsad1 p hp
    have h2 := hB p hp qs hqs
    nlinarith
  · intro u hu
    rw [hmaxmin] at hu ⊢
    rw [hg]
    refine le_trans ?_ (le_csSup ⟨KA + KB * |u|, ?_⟩ ⟨ps, hps, rfl⟩)
    · refine le_csInf (neY.image _) ?_
      rintro _ ⟨q, hq, rfl⟩
      have e : h u ps q = pairing B ps q * (R q ps - u) := by
        simp only [h, R]; field_simp [(hBpos ps hps q hq).ne']
      show d * (v - u) ≤ h u ps q
      rw [e]
      have h1 := hsad2 q hq
      have h2 := hB ps hps q hq
      nlinarith
    · rintro _ ⟨p, hp, rfl⟩
      exact hΨhi u p hp
  · intro u u'
    rw [hg, hg]
    refine sg_sup_pert X neX _ _ (KA + KB * |u'|) _ (fun p hp => hΨhi u' p hp) fun p hp => ?_
    refine sg_inf_pert Y neY _ _ (KA + KB * |u|) _ (fun q hq => (abs_le.1 (hbd u p hp q hq)).1)
      fun q hq => ?_
    simp only [h]
    have h1 := sg_pair_bound B p q hp hq
    have : pairing B p q * u' - pairing B p q * u ≤ KB * |u - u'| := by
      rw [← mul_sub]
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    linarith

lemma sg_ode (g : ℝ → ℝ) (hg : Continuous g) (v d : ℝ) (hd : 0 < d)
    (hsign : ∀ w, (w - v) * (g w + d * (w - v)) ≤ 0)
    (c : ℝ) (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Set.Ici 0))
    (hu : ∀ t : ℝ, 0 ≤ t → u t = c + ∫ s in (0 : ℝ)..t, g (u s)) :
    Tendsto u atTop (𝓝 v) := by
  have hgu : ContinuousOn (fun s => g (u s)) (Set.Ici 0) := hg.comp_continuousOn hu_cont
  have hderiv : ∀ t, 0 < t → HasDerivAt u (g (u t)) t := by
    intro t ht
    have hint : IntervalIntegrable (fun s => g (u s)) MeasureTheory.volume 0 t := by
      refine (hgu.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le ht.le]; exact Set.Icc_subset_Ici_self
    have hsm : StronglyMeasurableAtFilter (fun s => g (u s)) (𝓝 t) :=
      (hgu.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi t ht
    have hca : ContinuousAt (fun s => g (u s)) t :=
      hgu.continuousAt (Ici_mem_nhds ht)
    have hk := (intervalIntegral.integral_hasDerivAt_right hint hsm hca).const_add c
    refine hk.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact hu s (le_of_lt hs)
  let φ : ℝ → ℝ := fun t => (u t - v) ^ 2 * Real.exp (2 * d * t)
  have hφd : ∀ t, 0 < t → HasDerivAt φ
      (2 * (u t - v) * g (u t) * Real.exp (2 * d * t) +
        (u t - v) ^ 2 * (Real.exp (2 * d * t) * (2 * d))) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => (u t - v) ^ 2) (2 * (u t - v) * g (u t)) t := by
      exact (((hderiv t ht).sub_const v).pow 2).congr_deriv (by push_cast; ring)
    have h2 : HasDerivAt (fun t => Real.exp (2 * d * t)) (Real.exp (2 * d * t) * (2 * d)) t := by
      exact ((hasDerivAt_id t).const_mul (2 * d)).exp.congr_deriv (by simp)
    exact h1.mul h2
  have hanti : AntitoneOn φ (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact ((hu_cont.sub continuousOn_const).pow 2).mul (by fun_prop)
    · rw [interior_Ici]
      intro t ht
      exact (hφd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      rw [(hφd t ht).deriv]
      have := hsign (u t)
      have he := Real.exp_pos (2 * d * t)
      nlinarith
  have hu0 : u 0 = c := by rw [hu 0 le_rfl]; simp
  have hbound : ∀ t, 0 ≤ t → |u t - v| ≤ |c - v| * Real.exp (-(d * t)) := by
    intro t ht
    have h1 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
    simp only [φ, hu0, mul_zero, Real.exp_zero, mul_one] at h1
    have he : Real.exp (2 * d * t) = Real.exp (d * t) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [he] at h1
    have hpos : 0 < Real.exp (d * t) := Real.exp_pos _
    have h2 : (|u t - v| * Real.exp (d * t)) ^ 2 ≤ |c - v| ^ 2 := by
      rw [mul_pow, sq_abs, sq_abs]; exact h1
    have h3 : |u t - v| * Real.exp (d * t) ≤ |c - v| := by
      exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).1 h2
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact h3
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t => |c - v| * Real.exp (-(d * t))) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hd)
    simpa using this.const_mul |c - v|
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [Real.norm_eq_abs]
  exact hbound t ht

theorem scalar_core {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B : Matrix (Fin m) (Fin n) ℝ) (d : ℝ) (hd : 0 < d)
    (hB : ∀ p ∈ stdSimplex ℝ (Fin n), ∀ q ∈ stdSimplex ℝ (Fin m), d ≤ pairing B p q)
    (c : ℝ) (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Set.Ici 0))
    (hu : ∀ t : ℝ, 0 ≤ t → u t = c + ∫ s in (0 : ℝ)..t, gameRHS A B (u s)) :
    Tendsto u atTop (𝓝 (maxMinRatio A B)) ∧ maxMinRatio A B = minMaxRatio A B := by
  obtain ⟨heq, h1, h2, L, hL, hlip⟩ := sg_game hm hn A B d hd hB
  refine ⟨?_, heq⟩
  have hcont : Continuous (gameRHS A B) := by
    have : LipschitzWith (Real.toNNReal L) (gameRHS A B) := by
      refine LipschitzWith.of_dist_le' fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq, abs_le]
      constructor
      · have := hlip y x; rw [abs_sub_comm] at this; linarith
      · have := hlip x y; linarith
    exact this.continuous
  refine sg_ode (gameRHS A B) hcont (maxMinRatio A B) d hd (fun w => ?_) c u hu_cont hu
  rcases le_total (maxMinRatio A B) w with hw | hw
  · have := h1 w hw
    nlinarith
  · have := h2 w hw
    nlinarith

end BellmanDP.Markovian

open BellmanDP.Markovian
open Filter Topology

theorem solution {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B : Matrix (Fin m) (Fin n) ℝ) (d : ℝ) (hd : 0 < d)
    (hB : ∀ p ∈ stdSimplex ℝ (Fin n), ∀ q ∈ stdSimplex ℝ (Fin m), d ≤ pairing B p q)
    (c : ℝ) (u : ℝ → ℝ) (hu_cont : ContinuousOn u (Set.Ici 0))
    (hu : ∀ t : ℝ, 0 ≤ t → u t = c + ∫ s in (0 : ℝ)..t, gameRHS A B (u s)) :
    Tendsto u atTop (𝓝 (maxMinRatio A B)) ∧ maxMinRatio A B = minMaxRatio A B := by
  exact scalar_core hm hn A B d hd hB c u hu_cont hu
