-- Prove2me | solution 1 for FMLPricing.BranchBound.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:10:03.179222+00:00
-- url     : https://prove2.me/submissions/4bf78423-7cd9-46de-81af-e14cdcb0fc58

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

open FMLPricing.BranchBound

namespace FMLAlg

variable {m n : ℕ} (I : FML m n)

lemma denom_pos (c : Fin m) (p : Fin n → ℝ) : 0 < denom I c p := by
  unfold denom; positivity

lemma q0_pos (p : Fin n → ℝ) (c : Fin m) : 0 < q0 I p c := by
  unfold q0; exact one_div_pos.mpr (denom_pos I c p)

lemma q0_mono (hI : Standing I) {p p' : Fin n → ℝ} (h : p ≤ p') (c : Fin m) :
    q0 I p c ≤ q0 I p' c := by
  unfold q0
  apply one_div_le_one_div_of_le (denom_pos I c p')
  unfold denom
  refine (add_le_add_iff_left 1).mpr (Finset.sum_le_sum fun j _ => ?_)
  exact Real.exp_le_exp.mpr (by nlinarith [hI.b_pos j, h j])

lemma Xset_bounds (hI : Standing I) {x : Fin m → ℝ} (hx : x ∈ Xset I) (c : Fin m) :
    q0 I (pLo I) c ≤ x c ∧ x c ≤ q0 I (pHi I) c := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨q0_mono I hI hp.1 c, q0_mono I hI hp.2 c⟩

lemma s_mul_zOf (c : Fin m) (j : Fin n) (p : Fin n → ℝ) :
    s I c j * zOf I p j = Real.exp (I.a c j - I.b j * p j) := by
  unfold s zOf; rw [← Real.exp_add]; ring_nf

lemma q0_eq (c : Fin m) (p : Fin n → ℝ) :
    q0 I p c = 1 / (1 + ∑ j, s I c j * zOf I p j) := by
  unfold q0 denom; simp only [s_mul_zOf]

lemma sum_eq_of_q0 (c : Fin m) (p : Fin n → ℝ) :
    ∑ j, s I c j * zOf I p j = 1 / q0 I p c - 1 := by
  rw [q0_eq, one_div_one_div]; ring

lemma zOf_priceOf (hI : Standing I) {z : Fin n → ℝ} (hz : ∀ j, 0 < z j) :
    zOf I (priceOf I z) = z := by
  funext j
  unfold zOf priceOf
  rw [show -(-(I.b j)⁻¹ * Real.log (z j)) * I.b j = Real.log (z j) by
    field_simp [(hI.b_pos j).ne']]
  exact Real.exp_log (hz j)

lemma zLo_pos (j : Fin n) : 0 < zLo I j := Real.exp_pos _

lemma zOf_mem (hI : Standing I) {p : Fin n → ℝ} (hp : p ∈ priceBox I) :
    zOf I p ∈ Set.Icc (zLo I) (zHi I) :=
  ⟨fun j => Real.exp_le_exp.mpr (by nlinarith [hp.2 j, hI.b_pos j]),
   fun j => Real.exp_le_exp.mpr (by nlinarith [hp.1 j, hI.b_pos j])⟩

lemma priceOf_mem (hI : Standing I) {z : Fin n → ℝ} (hz : z ∈ Set.Icc (zLo I) (zHi I)) :
    priceOf I z ∈ priceBox I := by
  have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1 j)
  have h := zOf_priceOf I hI hpos
  constructor <;> intro j
  · have h2 := hz.2 j
    rw [← h] at h2
    unfold zOf zHi at h2
    have := Real.exp_le_exp.mp h2
    nlinarith [hI.b_pos j]
  · have h2 := hz.1 j
    rw [← h] at h2
    unfold zOf zLo at h2
    have := Real.exp_le_exp.mp h2
    nlinarith [hI.b_pos j]

lemma mu_eq {t : ℝ} (ht : 0 < t) : (1 - t) / t = 1 / t - 1 := by
  field_simp

lemma mu_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (1 - b) / b ≤ (1 - a) / a := by
  rw [mu_eq (ha.trans_le hab), mu_eq ha]
  have := one_div_le_one_div_of_le ha hab
  linarith

lemma xLo_pos (x : Fin m → ℝ) (r : ℝ) (c : Fin m) : 0 < xLo I x r c :=
  (q0_pos I _ c).trans_le (le_max_right _ _)

lemma xHi_pos {x : Fin m → ℝ} {r : ℝ} (hx : ∀ c, 0 < x c) (hr : 0 < r) (c : Fin m) :
    0 < xHi I x r c :=
  lt_min (by linarith [hx c]) (q0_pos I _ c)

/-- Every feasible point of `LP(x, r)` gives `χ(x, δ⁺, δ⁻) ∈ R(x, r) ∩ X`. -/
lemma chi_mem (hI : Standing I) {x : Fin m → ℝ} (hx : ∀ c, 0 < x c) {r : ℝ} (hr : 0 < r)
    {v : LPVars m n} (hv : LPFeasibleAt I x r v) :
    chi x v.δp v.δm ∈ Rbox I x r ∩ Xset I := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hv
  have hzpos : ∀ j, 0 < v.z j := fun j => (zLo_pos I j).trans_le (h5 j).1
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hI.n_pos⟩, Finset.mem_univ _⟩
  have hy : ∀ c, 0 < ∑ j, s I c j * v.z j := fun c =>
    Finset.sum_pos (fun j _ => mul_pos (Real.exp_pos _) (hzpos j)) hne
  have hchi : ∀ c, chi x v.δp v.δm c = 1 / (1 + ∑ j, s I c j * v.z j) := by
    intro c
    have e : v.δm c - v.δp c = (∑ j, s I c j * v.z j) - (1 - x c) / x c := by
      have := h1 c; unfold mu at this; linarith
    unfold chi
    rw [e]
    have hxc := (hx c).ne'
    have hyc := hy c
    rw [div_eq_div_iff (by field_simp; nlinarith [hx c]) (by linarith)]
    field_simp
    ring
  have hmem : priceOf I v.z ∈ priceBox I := priceOf_mem I hI ⟨fun j => (h5 j).1, fun j => (h5 j).2⟩
  have hq : chi x v.δp v.δm = q0 I (priceOf I v.z) := by
    funext c
    rw [hchi, q0_eq, zOf_priceOf I hI hzpos]
  refine ⟨⟨fun c => ?_, fun c => ?_⟩, hq ▸ ⟨_, hmem, rfl⟩⟩
  · -- lower end
    have h4c := h4 c
    have e := h1 c
    have hlo := xLo_pos I x r c
    have hyl : ∑ j, s I c j * v.z j ≤ (1 - xLo I x r c) / xLo I x r c := by
      unfold mu at h4c e; linarith
    rw [le_div_iff₀ hlo] at hyl
    show xLo I x r c ≤ chi x v.δp v.δm c
    rw [hchi, le_div_iff₀ (by linarith [hy c])]
    linarith
  · have h3c := h3 c
    have e := h1 c
    have hhi := xHi_pos I hx hr c
    have hyl : (1 - xHi I x r c) / xHi I x r c ≤ ∑ j, s I c j * v.z j := by
      unfold mu at h3c e; linarith
    rw [div_le_iff₀ hhi] at hyl
    show chi x v.δp v.δm c ≤ xHi I x r c
    rw [hchi, div_le_iff₀ (by linarith [hy c])]
    linarith

lemma zOf_inj (hI : Standing I) : Function.Injective (zOf I) := by
  intro p p' h
  funext j
  have := congrFun h j
  unfold zOf at this
  have := Real.exp_injective this
  have hb := (hI.b_pos j).ne'
  have : (p j - p' j) * I.b j = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · linarith
  · exact absurd h1 hb

lemma q_eq_of (c : Fin m) (j : Fin n) (p : Fin n → ℝ) :
    q I c j p = s I c j * zOf I p j * q0 I p c := by
  unfold q q0
  rw [s_mul_zOf]; ring

lemma obj_eq (hI : Standing I) (x : Fin m → ℝ) (p : Fin n → ℝ) (hq : ∀ c, q0 I p c = x c) :
    Pi I p = cnstrObj I x (zOf I p) := by
  have hlog : ∀ j, Real.log (zOf I p j) = -(p j) * I.b j := fun j => by
    unfold zOf; rw [Real.log_exp]
  have hqq : ∀ c j, q I c j p = s I c j * zOf I p j * x c := fun c j => by
    rw [q_eq_of, hq]
  unfold Pi cnstrObj kx
  simp only [hqq, hlog]
  calc ∑ c, I.w c * ∑ j, p j * (s I c j * zOf I p j * x c)
      = ∑ c, ∑ j, I.w c * (p j * (s I c j * zOf I p j * x c)) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ j, ∑ c, I.w c * (p j * (s I c j * zOf I p j * x c)) := Finset.sum_comm
    _ = -∑ j, zOf I p j * (-p j * I.b j) * ((I.b j)⁻¹ * ∑ c, I.w c * s I c j * x c) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hb := (hI.b_pos j).ne'
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        field_simp

theorem lemma1 (hI : Standing I) (x : Fin m → ℝ) (hx : x ∈ Xset I) :
    Set.BijOn (zOf I) {p | p ∈ priceBox I ∧ ∀ c, q0 I p c = x c} (cnstrFeasible I x) ∧
      (∀ p ∈ priceBox I, (∀ c, q0 I p c = x c) → Pi I p = cnstrObj I x (zOf I p)) ∧
      ConcaveOn ℝ (Set.Icc (zLo I) (zHi I)) (cnstrObj I x) := by
  refine ⟨⟨?_, (zOf_inj I hI).injOn, ?_⟩, fun p _ hq => obj_eq I hI x p hq, ?_⟩
  · rintro p ⟨hp, hq⟩
    refine ⟨zOf_mem I hI hp, fun c => ?_⟩
    rw [← hq c, q0_eq, one_div_one_div]
  · rintro z ⟨hz, hzc⟩
    have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1 j)
    refine ⟨priceOf I z, ⟨priceOf_mem I hI hz, fun c => ?_⟩, zOf_priceOf I hI hpos⟩
    rw [q0_eq, zOf_priceOf I hI hpos, hzc c, one_div_one_div]
  · have hxpos : ∀ c, 0 < x c := by
      obtain ⟨p, -, rfl⟩ := hx
      exact fun c => q0_pos I p c
    have hk : ∀ j, 0 ≤ kx I j x := fun j => by
      unfold kx
      exact mul_nonneg (inv_pos.mpr (hI.b_pos j)).le
        (Finset.sum_nonneg fun c _ => by
          have := hI.w_pos c; have := Real.exp_pos (I.a c j); have := hxpos c
          unfold s; positivity)
    have hf : ∀ w : Fin n → ℝ, cnstrObj I x w = ∑ j, kx I j x * Real.negMulLog (w j) := by
      intro w
      unfold cnstrObj Real.negMulLog
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    refine ⟨convex_Icc _ _, ?_⟩
    intro u hu v hv a b ha hb hab
    rw [hf, hf, hf]
    simp only [smul_eq_mul, Pi.add_apply, Pi.smul_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hu0 : u j ∈ Set.Ici (0 : ℝ) := ((zLo_pos I j).trans_le (hu.1 j)).le
    have hv0 : v j ∈ Set.Ici (0 : ℝ) := ((zLo_pos I j).trans_le (hv.1 j)).le
    have h := Real.concaveOn_negMulLog.2 hu0 hv0 ha hb hab
    simp only [smul_eq_mul] at h
    have := mul_le_mul_of_nonneg_left h (hk j)
    linarith

lemma feas_eq (x : Fin m → ℝ) : cnstrFeasible I x =
    Set.Icc (zLo I) (zHi I) ∩ ⋂ c, {z | 1 + ∑ j, s I c j * z j = 1 / x c} := by
  ext z; simp [cnstrFeasible]

lemma feas_compact (x : Fin m → ℝ) : IsCompact (cnstrFeasible I x) := by
  rw [feas_eq]
  exact isCompact_Icc.inter_right (isClosed_iInter fun c => isClosed_eq (by fun_prop)
    continuous_const)

lemma obj_cont (x : Fin m → ℝ) : Continuous (cnstrObj I x) := by
  unfold cnstrObj
  fun_prop

lemma piX_eq_of_max {x : Fin m → ℝ} {z : Fin n → ℝ} (hz : IsCnstrMax I x z) :
    piX I x = cnstrObj I x z := by
  have : IsGreatest (cnstrObj I x '' cnstrFeasible I x) (cnstrObj I x z) :=
    ⟨Set.mem_image_of_mem _ hz.1, by rintro _ ⟨z', hz', rfl⟩; exact hz.2 z' hz'⟩
  exact this.csSup_eq

lemma le_piX {x : Fin m → ℝ} {z : Fin n → ℝ} (hz : z ∈ cnstrFeasible I x) :
    cnstrObj I x z ≤ piX I x :=
  le_csSup ((feas_compact I x).bddAbove_image (obj_cont I x).continuousOn)
    (Set.mem_image_of_mem _ hz)

lemma q0_priceOf_of_feas (hI : Standing I) {x : Fin m → ℝ} {z : Fin n → ℝ}
    (hz : z ∈ cnstrFeasible I x) : ∀ c, q0 I (priceOf I z) c = x c := by
  intro c
  have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1.1 j)
  rw [q0_eq, zOf_priceOf I hI hpos, hz.2 c, one_div_one_div]

lemma Pi_priceOf_of_feas (hI : Standing I) {x : Fin m → ℝ} {z : Fin n → ℝ}
    (hz : z ∈ cnstrFeasible I x) : Pi I (priceOf I z) = cnstrObj I x z := by
  have hpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1.1 j)
  rw [obj_eq I hI x _ (q0_priceOf_of_feas I hI hz), zOf_priceOf I hI hpos]

lemma piX_spec (hI : Standing I) {x : Fin m → ℝ} (hx : x ∈ Xset I) :
    (∃ p ∈ priceBox I, (∀ c, q0 I p c = x c) ∧ piX I x = Pi I p) ∧
      ∀ p ∈ priceBox I, (∀ c, q0 I p c = x c) → Pi I p ≤ piX I x := by
  have hne : (cnstrFeasible I x).Nonempty := by
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨zOf I p, zOf_mem I hI hp, fun c => by rw [q0_eq, one_div_one_div]⟩
  obtain ⟨z, hz, hmax⟩ := (feas_compact I x).exists_isMaxOn hne (obj_cont I x).continuousOn
  have hzm : IsCnstrMax I x z := ⟨hz, fun z' hz' => hmax hz'⟩
  refine ⟨⟨priceOf I z, priceOf_mem I hI hz.1, q0_priceOf_of_feas I hI hz, ?_⟩, ?_⟩
  · rw [piX_eq_of_max I hzm, Pi_priceOf_of_feas I hI hz]
  · intro p hp hq
    rw [obj_eq I hI x p hq]
    exact le_piX I ⟨zOf_mem I hI hp, fun c => by rw [← hq c, q0_eq, one_div_one_div]⟩

lemma q_pos (c : Fin m) (i : Fin n) (p : Fin n → ℝ) : 0 < q I c i p := by
  unfold q; exact div_pos (Real.exp_pos _) (denom_pos I c p)

lemma term_le (hI : Standing I) (c : Fin m) (i : Fin n) (p : Fin n → ℝ) :
    p i * q I c i p ≤ Real.exp (I.a c i - 1) / I.b i := by
  have hb := hI.b_pos i
  have hq := q_pos I c i p
  rcases le_or_gt (p i) 0 with hp | hp
  · have : p i * q I c i p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hq.le
    exact this.trans (div_pos (Real.exp_pos _) hb).le
  · have hqle : q I c i p ≤ Real.exp (I.a c i - I.b i * p i) := by
      unfold q
      apply div_le_self (Real.exp_pos _).le
      unfold denom
      have : 0 ≤ ∑ j, Real.exp (I.a c j - I.b j * p j) :=
        Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
      linarith
    have h1 : p i * q I c i p ≤ p i * Real.exp (I.a c i - I.b i * p i) :=
      mul_le_mul_of_nonneg_left hqle hp.le
    have h2 : I.b i * p i ≤ Real.exp (I.b i * p i - 1) := by
      have := Real.add_one_le_exp (I.b i * p i - 1); linarith
    have h3 : Real.exp (I.a c i - I.b i * p i) * Real.exp (I.b i * p i - 1)
        = Real.exp (I.a c i - 1) := by rw [← Real.exp_add]; ring_nf
    rw [le_div_iff₀ hb]
    have he := Real.exp_pos (I.a c i - I.b i * p i)
    calc p i * q I c i p * I.b i ≤ p i * Real.exp (I.a c i - I.b i * p i) * I.b i :=
          mul_le_mul_of_nonneg_right h1 hb.le
      _ = Real.exp (I.a c i - I.b i * p i) * (I.b i * p i) := by ring
      _ ≤ Real.exp (I.a c i - I.b i * p i) * Real.exp (I.b i * p i - 1) :=
          mul_le_mul_of_nonneg_left h2 he.le
      _ = Real.exp (I.a c i - 1) := h3

lemma segRev_bdd (hI : Standing I) (c : Fin m) :
    BddAbove (Set.range fun p : Fin n → ℝ => ∑ i, p i * q I c i p) := by
  refine ⟨∑ i, Real.exp (I.a c i - 1) / I.b i, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact Finset.sum_le_sum fun i _ => term_le I hI c i p

lemma segRev_pLo_pos (hI : Standing I) (c : Fin m) :
    0 < ∑ i, pLo I i * q I c i (pLo I) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hI.n_pos⟩, Finset.mem_univ _⟩
  exact Finset.sum_pos (fun i _ => mul_pos (inv_pos.mpr (hI.b_pos i)) (q_pos I c i _)) hne

lemma segMax_pos (hI : Standing I) (c : Fin m) : 0 < segMax I c :=
  (segRev_pLo_pos I hI c).trans_le (le_csSup (segRev_bdd I hI c) ⟨pLo I, rfl⟩)

lemma pLo_lt_pHi (hI : Standing I) (j : Fin n) : pLo I j < pHi I j := by
  have hc : 0 < segMax I ⟨0, hI.m_pos⟩ := segMax_pos I hI _
  have : segMax I ⟨0, hI.m_pos⟩ ≤ ⨆ c : Fin m, segMax I c :=
    le_ciSup (Finite.bddAbove_range _) _
  simp only [pLo, pHi]; linarith

lemma pLo_mem (hI : Standing I) : pLo I ∈ priceBox I :=
  ⟨le_rfl, fun j => (pLo_lt_pHi I hI j).le⟩

lemma Pi_cont : Continuous (Pi I) := by
  unfold Pi
  refine continuous_finset_sum _ fun c _ => continuous_const.mul
    (continuous_finset_sum _ fun j _ => (continuous_apply j).mul ?_)
  unfold q
  refine Continuous.div (by fun_prop) ?_ (fun p => (denom_pos I c p).ne')
  unfold denom; fun_prop

/-- Equation (5) in the strong form: a maximizer `p₀` of `Π` on the box gives a maximizer
`q_0(p₀)` of `π` on `X`, with the same value. -/
lemma eq5_core (hI : Standing I) {p₀ : Fin n → ℝ} (hp₀ : p₀ ∈ priceBox I)
    (hmax : ∀ p ∈ priceBox I, Pi I p ≤ Pi I p₀) :
    q0 I p₀ ∈ Xset I ∧ piX I (q0 I p₀) = Pi I p₀ ∧ ∀ x ∈ Xset I, piX I x ≤ Pi I p₀ := by
  have hx₀ : q0 I p₀ ∈ Xset I := ⟨p₀, hp₀, rfl⟩
  have hle : ∀ x ∈ Xset I, piX I x ≤ Pi I p₀ := by
    intro x hx
    obtain ⟨⟨p, hp, -, he⟩, -⟩ := piX_spec I hI hx
    rw [he]; exact hmax p hp
  refine ⟨hx₀, le_antisymm (hle _ hx₀) ((piX_spec I hI hx₀).2 p₀ hp₀ fun c => rfl), hle⟩

lemma exists_box_max (hI : Standing I) :
    ∃ p₀ ∈ priceBox I, ∀ p ∈ priceBox I, Pi I p ≤ Pi I p₀ := by
  obtain ⟨p₀, hp₀, h⟩ := (isCompact_Icc : IsCompact (priceBox I)).exists_isMaxOn
    ⟨pLo I, pLo_mem I hI⟩ (Pi_cont I).continuousOn
  exact ⟨p₀, hp₀, fun p hp => h hp⟩

lemma exists_max (hI : Standing I) {x : Fin m → ℝ} (hx : x ∈ Xset I) :
    ∃ z, IsCnstrMax I x z := by
  have hne : (cnstrFeasible I x).Nonempty := by
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨zOf I p, zOf_mem I hI hp, fun c => by rw [q0_eq, one_div_one_div]⟩
  obtain ⟨z, hz, hmax⟩ := (feas_compact I x).exists_isMaxOn hne (obj_cont I x).continuousOn
  exact ⟨z, hz, fun z' hz' => hmax hz'⟩

lemma xiFeas_eq (x : Fin m → ℝ) (r : ℝ) : xiFeasible I x r =
    Set.Icc (fun c j => zLo I j * xLo I x r c) (fun c j => zHi I j * xHi I x r c) ∩
      ⋂ c, ({ξ : Fin m → Fin n → ℝ | 1 - xHi I x r c ≤ ∑ j, s I c j * ξ c j} ∩
        {ξ | ∑ j, s I c j * ξ c j ≤ 1 - xLo I x r c}) := by
  ext ξ
  simp only [xiFeasible, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, Set.mem_iInter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun c j => (h1 c j).1, fun c j => (h1 c j).2⟩, fun c => h2 c⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun c j => ⟨h1 c j, h2 c j⟩, h3⟩

lemma xiFeas_compact (x : Fin m → ℝ) (r : ℝ) : IsCompact (xiFeasible I x r) := by
  rw [xiFeas_eq]
  exact isCompact_Icc.inter_right (isClosed_iInter fun c =>
    (isClosed_le continuous_const (by fun_prop)).inter (isClosed_le (by fun_prop) continuous_const))

lemma xiObj_cont {x : Fin m → ℝ} {r : ℝ} (hpos : ∀ c, 0 < xHi I x r c) :
    Continuous (xiObj I x r) := by
  have : xiObj I x r = fun ξ => -∑ c, ∑ j, xHi I x r c * ((ξ c j / xHi I x r c) *
      Real.log (ξ c j / xHi I x r c)) * s I c j * I.w c * (I.b j)⁻¹ := by
    funext ξ
    unfold xiObj
    congr 1
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
    have := (hpos c).ne'
    field_simp
  rw [this]
  fun_prop

theorem prop6 (hI : Standing I)
    (x : Fin m → ℝ) (hx : x ∈ Xset I) (r : ℝ) (hr : 0 < r) :
    ∀ x' ∈ Rbox I x r ∩ Xset I, piX I x' ≤ piXi I x r := by
  rintro x' ⟨hR, hX'⟩
  have hxpos : ∀ c, 0 < x c := by
    obtain ⟨p, -, rfl⟩ := hx; exact fun c => q0_pos I p c
  have hx'pos : ∀ c, 0 < x' c := by
    obtain ⟨p, -, rfl⟩ := hX'; exact fun c => q0_pos I p c
  have hHi := xHi_pos I hxpos hr
  obtain ⟨z, hz⟩ := exists_max I hI hX'
  have hzpos : ∀ j, 0 < z j := fun j => (zLo_pos I j).trans_le (hz.1.1.1 j)
  set ξ : Fin m → Fin n → ℝ := fun c j => z j * x' c with hξ
  have hfeas : ξ ∈ xiFeasible I x r := by
    refine ⟨fun c j => ⟨?_, ?_⟩, fun c => ?_⟩
    · exact mul_le_mul (hz.1.1.1 j) (hR.1 c) (xLo_pos I x r c).le (hzpos j).le
    · exact mul_le_mul (hz.1.1.2 j) (hR.2 c) (hx'pos c).le ((zLo_pos I j).trans_le
        ((hz.1.1.1 j).trans (hz.1.1.2 j))).le
    · have hs : ∑ j, s I c j * ξ c j = 1 - x' c := by
        have h2 := hz.1.2 c
        have : ∑ j, s I c j * ξ c j = x' c * ∑ j, s I c j * z j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; simp only [hξ]; ring
        rw [this]
        have : ∑ j, s I c j * z j = 1 / x' c - 1 := by linarith
        rw [this]; field_simp [(hx'pos c).ne']
      rw [hs]
      exact ⟨by linarith [hR.2 c], by linarith [hR.1 c]⟩
  have hbdd : BddAbove (xiObj I x r '' xiFeasible I x r) :=
    (xiFeas_compact I x r).bddAbove_image (xiObj_cont I hHi).continuousOn
  have hle : cnstrObj I x' z ≤ xiObj I x r ξ := by
    have e1 : cnstrObj I x' z = ∑ c, ∑ j,
        -(z j * x' c * s I c j * I.w c * (I.b j)⁻¹) * Real.log (z j) := by
      unfold cnstrObj kx
      rw [← Finset.sum_neg_distrib, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    have e2 : xiObj I x r ξ = ∑ c, ∑ j,
        -(z j * x' c * s I c j * I.w c * (I.b j)⁻¹) * Real.log (ξ c j / xHi I x r c) := by
      unfold xiObj
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hξ]; ring
    rw [e1, e2]
    refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun j _ => ?_
    have hT : 0 ≤ z j * x' c * s I c j * I.w c * (I.b j)⁻¹ := by
      have := hzpos j; have := hx'pos c; have := hI.w_pos c; have := hI.b_pos j
      unfold s; positivity
    have hlog : Real.log (ξ c j / xHi I x r c) ≤ Real.log (z j) := by
      apply Real.log_le_log (div_pos (mul_pos (hzpos j) (hx'pos c)) (hHi c))
      rw [div_le_iff₀ (hHi c)]
      show z j * x' c ≤ z j * xHi I x r c
      exact mul_le_mul_of_nonneg_left (hR.2 c) (hzpos j).le
    nlinarith
  rw [piX_eq_of_max I hz]
  exact hle.trans (le_csSup hbdd (Set.mem_image_of_mem _ hfeas))

end FMLAlg

theorem solution {m n : ℕ} (I : FML m n) (hI : Standing I)
    (x : Fin m → ℝ) (hx : x ∈ Xset I) (r : ℝ) (hr : 0 < r) :
    ∀ x' ∈ Rbox I x r ∩ Xset I, piX I x' ≤ piXi I x r :=
  FMLAlg.prop6 I hI x hx r hr
