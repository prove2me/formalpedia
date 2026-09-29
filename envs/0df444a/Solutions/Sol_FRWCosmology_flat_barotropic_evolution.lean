-- Prove2me | solution 1 for FRWCosmology.flat_barotropic_evolution
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T19:29:24.905013+00:00
-- url     : https://prove2.me/submissions/90a12116-8fb2-45ac-9a0f-c7b7d1fe1249

import Definitions.Def_FRWUniverse

open FRWCosmology

theorem W2c_FRWCosmology_accel (U : FRWUniverse) (t : ℝ) (ht : t ∈ U.I) :
    U.addot t / U.a t = -(4 * Real.pi * U.G / 3) * (U.rho t + 3 * U.p t) := by
  have h1 := U.friedmann₁ t ht
  have h2 := U.friedmann₂ t ht
  linear_combination h2 + h1

theorem W2c_FRWCosmology_Hdot (U : FRWUniverse) (x : ℝ) (hx : x ∈ U.I) :
    (U.addot x * U.a x - U.adot x * U.adot x) / U.a x ^ 2
      = U.addot x / U.a x - (U.adot x / U.a x) ^ 2 := by
  have hax := (U.a_pos x hx).ne'
  field_simp
  try ring

theorem W2c_FRWCosmology_cont (U : FRWUniverse) (hG : U.G ≠ 0) (t : ℝ) (ht : t ∈ U.I) :
    U.rhodot t + 3 * U.H t * (U.rho t + U.p t) = 0 := by
  have ha := U.a_pos t ht
  have hev : (fun s => (U.adot s / U.a s) * (U.adot s / U.a s)) =ᶠ[nhds t]
      (fun s => 8 * Real.pi * U.G / 3 * U.rho s - U.K / (U.a s * U.a s)) := by
    filter_upwards [U.I_open.mem_nhds ht] with s hs
    have := U.friedmann₁ s hs
    simp only [sq] at this
    exact this
  have hH : HasDerivAt (fun s => U.adot s / U.a s)
      ((U.addot t * U.a t - U.adot t * U.adot t) / U.a t ^ 2) t :=
    (U.hadot t ht).div (U.ha t ht) ha.ne'
  have hR : HasDerivAt (fun s => 8 * Real.pi * U.G / 3 * U.rho s - U.K / (U.a s * U.a s))
      (8 * Real.pi * U.G / 3 * U.rhodot t -
        (0 * (U.a t * U.a t) - U.K * (U.adot t * U.a t + U.a t * U.adot t)) /
          (U.a t * U.a t) ^ 2) t :=
    ((U.hrho t ht).const_mul (8 * Real.pi * U.G / 3)).sub
    ((hasDerivAt_const t U.K).div ((U.ha t ht).mul (U.ha t ht)) (mul_ne_zero ha.ne' ha.ne'))
  have hHH : HasDerivAt (fun s => (U.adot s / U.a s) * (U.adot s / U.a s))
      ((U.addot t * U.a t - U.adot t * U.adot t) / U.a t ^ 2 * (U.adot t / U.a t) +
        U.adot t / U.a t * ((U.addot t * U.a t - U.adot t * U.adot t) / U.a t ^ 2)) t :=
    hH.mul hH
  have e := hev.deriv_eq
  rw [hHH.deriv, hR.deriv] at e
  have hK : (0 * (U.a t * U.a t) - U.K * (U.adot t * U.a t + U.a t * U.adot t)) /
      (U.a t * U.a t) ^ 2 = -(2 * (U.adot t / U.a t) * (U.K / U.a t ^ 2)) := by
    have hax := ha.ne'
    field_simp
    ring
  rw [W2c_FRWCosmology_Hdot U t ht, hK, U.friedmann₂ t ht] at e
  have key : 8 * Real.pi * U.G / 3 * (U.rhodot t + 3 * U.H t * (U.rho t + U.p t)) = 0 := by
    unfold FRWUniverse.H
    linear_combination (-1 : ℝ) * e
  rcases mul_eq_zero.1 key with h | h
  · exfalso
    have : 8 * Real.pi * U.G / 3 ≠ 0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hG) (by norm_num)
    exact this h
  · exact h

theorem W2c_FRWCosmology_density (U : FRWUniverse) (hG : U.G ≠ 0) (w : ℝ)
    (hw : U.LinearEoS w)
    (s : ℝ) (hs : s ∈ U.I) (t : ℝ) (ht : t ∈ U.I) :
    U.rho t * U.a t ^ (3 * (1 + w)) = U.rho s * U.a s ^ (3 * (1 + w)) := by
  have hd : ∀ x ∈ U.I, HasDerivAt (fun y => U.rho y * U.a y ^ (3 * (1 + w)))
      (U.rhodot x * U.a x ^ (3 * (1 + w)) +
        U.rho x * (U.adot x * (3 * (1 + w)) * U.a x ^ (3 * (1 + w) - 1))) x :=
    fun x hx => (U.hrho x hx).mul ((U.ha x hx).rpow_const (Or.inl (U.a_pos x hx).ne'))
  exact U.I_open.is_const_of_deriv_eq_zero (f := fun y => U.rho y * U.a y ^ (3 * (1 + w)))
    U.I_conn (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      simp only [Pi.zero_apply]
      rw [(hd x hx).deriv]
      have hc := W2c_FRWCosmology_cont U hG x hx
      have hax := U.a_pos x hx
      unfold FRWUniverse.H at hc
      rw [hw x hx] at hc
      rw [Real.rpow_sub_one hax.ne']
      have : U.rhodot x = -(3 * (U.adot x / U.a x) * (U.rho x + w * U.rho x)) := by linarith
      rw [this]
      ring) ht hs

theorem W2c_FRWCosmology_de_sitter (U : FRWUniverse) (hG : U.G ≠ 0) (hK : U.K = 0)
    (hw : U.LinearEoS (-1)) :
    ∃ H₀ : ℝ, ∀ s ∈ U.I, ∀ t ∈ U.I, U.a t = U.a s * Real.exp (H₀ * (t - s)) := by
  have hH : ∀ x ∈ U.I, HasDerivAt (fun s => U.adot s / U.a s)
      ((U.addot x * U.a x - U.adot x * U.adot x) / U.a x ^ 2) x :=
    fun x hx => (U.hadot x hx).div (U.ha x hx) (U.a_pos x hx).ne'
  have hH0 : ∀ x ∈ U.I, (U.addot x * U.a x - U.adot x * U.adot x) / U.a x ^ 2 = 0 := by
    intro x hx
    have h2 := U.friedmann₂ x hx
    rw [hw x hx, hK] at h2
    rw [W2c_FRWCosmology_Hdot U x hx, h2]
    ring
  obtain ⟨H₀, hHc⟩ := U.I_open.exists_is_const_of_deriv_eq_zero
    (f := fun s => U.adot s / U.a s) U.I_conn
    (fun x hx => (hH x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by simp only [Pi.zero_apply]; rw [(hH x hx).deriv, hH0 x hx])
  refine ⟨H₀, fun s hs t ht => ?_⟩
  have hg : ∀ x ∈ U.I, HasDerivAt (fun y => U.a y * Real.exp (-H₀ * y))
      (U.adot x * Real.exp (-H₀ * x) + U.a x * (Real.exp (-H₀ * x) * (-H₀ * 1))) x :=
    fun x hx => (U.ha x hx).mul ((hasDerivAt_id' x).const_mul (-H₀)).exp
  have hc := U.I_open.is_const_of_deriv_eq_zero
    (f := fun y => U.a y * Real.exp (-H₀ * y)) U.I_conn
    (fun x hx => (hg x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      simp only [Pi.zero_apply]
      rw [(hg x hx).deriv]
      have h1 := hHc x hx
      have hax := (U.a_pos x hx).ne'
      have : U.adot x = H₀ * U.a x := by rw [← h1, div_mul_cancel₀ _ hax]
      rw [this]; ring) ht hs
  try simp only at hc
  calc U.a t = U.a t * Real.exp (-H₀ * t) * Real.exp (H₀ * t) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ = U.a s * Real.exp (-H₀ * s) * Real.exp (H₀ * t) := by rw [hc]
    _ = U.a s * Real.exp (H₀ * (t - s)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem W2c_FRWCosmology_hinv (U : FRWUniverse) (hG : 0 < U.G) (hK : U.K = 0) (w : ℝ)
    (hw : w ≠ -1) (heos : U.LinearEoS w) (hrho : ∀ t ∈ U.I, 0 < U.rho t) :
    ∃ t₀ : ℝ, ∀ t ∈ U.I, U.H t ≠ 0 ∧ U.H t * (3 / 2 * (1 + w) * (t - t₀)) = 1 := by
  have hc : 3 / 2 * (1 + w) ≠ 0 := by
    intro h; apply hw; linarith
  have h1w : 1 + w ≠ 0 := by intro h; apply hw; linarith
  have hπ := Real.pi_pos
  have hHne : ∀ x ∈ U.I, U.adot x / U.a x ≠ 0 := by
    intro x hx h
    have h1 := U.friedmann₁ x hx
    rw [h, hK] at h1
    have := hrho x hx
    have : 0 < 8 * Real.pi * U.G / 3 * U.rho x := by positivity
    have e0 : (0:ℝ) ^ 2 = 0 := by norm_num
    have e1 : (0:ℝ) / U.a x ^ 2 = 0 := zero_div _
    linarith
  have hderiv : ∀ x ∈ U.I, (U.addot x * U.a x - U.adot x * U.adot x) / U.a x ^ 2
      = -(3 / 2 * (1 + w)) * (U.adot x / U.a x) ^ 2 := by
    intro x hx
    have h1 := U.friedmann₁ x hx
    have h2 := U.friedmann₂ x hx
    rw [heos x hx, hK] at h2
    rw [hK] at h1
    rw [W2c_FRWCosmology_Hdot U x hx, h2, h1]
    ring
  have hg : ∀ x ∈ U.I, HasDerivAt (fun s => (U.adot s / U.a s)⁻¹ - 3 / 2 * (1 + w) * s)
      (-((U.addot x * U.a x - U.adot x * U.adot x) / U.a x ^ 2) / (U.adot x / U.a x) ^ 2
        - 3 / 2 * (1 + w) * 1) x :=
    fun x hx => (((U.hadot x hx).div (U.ha x hx) (U.a_pos x hx).ne').inv (hHne x hx)).sub
      ((hasDerivAt_id' x).const_mul _)
  obtain ⟨C, hC⟩ := U.I_open.exists_is_const_of_deriv_eq_zero
    (f := fun s => (U.adot s / U.a s)⁻¹ - 3 / 2 * (1 + w) * s) U.I_conn
    (fun x hx => (hg x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      simp only [Pi.zero_apply]
      rw [(hg x hx).deriv, hderiv x hx]
      have hH2 := hHne x hx
      generalize U.adot x / U.a x = H at hH2 ⊢
      field_simp
      try ring)
  refine ⟨-C / (3 / 2 * (1 + w)), fun t ht => ⟨hHne t ht, ?_⟩⟩
  have h1 := hC t ht
  try simp only at h1
  unfold FRWUniverse.H
  have hH := hHne t ht
  generalize U.adot t / U.a t = H at h1 hH ⊢
  have hcc : 3 / 2 * (1 + w) * (-C / (3 / 2 * (1 + w))) = -C := by field_simp
  have : 3 / 2 * (1 + w) * (t - -C / (3 / 2 * (1 + w))) = H⁻¹ := by
    rw [mul_sub, hcc]; linarith
  rw [this, mul_inv_cancel₀ hH]

theorem W2c_FRWCosmology_hubble (U : FRWUniverse) (hG : 0 < U.G) (hK : U.K = 0) (w : ℝ)
    (hw : w ≠ -1)
    (heos : U.LinearEoS w) (hrho : ∀ t ∈ U.I, 0 < U.rho t) :
    ∃ t₀ : ℝ, ∀ t ∈ U.I, U.H t = 2 / (3 * (1 + w) * (t - t₀)) := by
  obtain ⟨t₀, h⟩ := W2c_FRWCosmology_hinv U hG hK w hw heos hrho
  refine ⟨t₀, fun t ht => ?_⟩
  have h1 := (h t ht).2
  have hX : 3 * (1 + w) * (t - t₀) ≠ 0 := by
    intro h0
    have : 3 / 2 * (1 + w) * (t - t₀) = 0 := by linear_combination h0 / 2
    rw [this, mul_zero] at h1
    exact zero_ne_one h1
  rw [eq_div_iff hX]
  linear_combination 2 * h1

theorem W2c_FRWCosmology_flat (U : FRWUniverse) (hG : 0 < U.G) (hK : U.K = 0) (w : ℝ)
    (hw : w ≠ -1) (heos : U.LinearEoS w) (hrho : ∀ t ∈ U.I, 0 < U.rho t) :
    ∃ t₀ : ℝ, (∀ t ∈ U.I, t ≠ t₀) ∧
      ∀ s ∈ U.I, ∀ t ∈ U.I,
        U.a t = U.a s * ((t - t₀) / (s - t₀)) ^ (2 / (3 * (1 + w))) ∧
        U.rho t = U.rho s * ((s - t₀) / (t - t₀)) ^ 2 := by
  obtain ⟨t₀, h⟩ := W2c_FRWCosmology_hinv U hG hK w hw heos hrho
  have h1w : 1 + w ≠ 0 := by intro h0; apply hw; linarith
  have hπ := Real.pi_pos
  have hπ' := Real.pi_ne_zero
  have hG' := hG.ne'
  have hne : ∀ t ∈ U.I, t ≠ t₀ := by
    intro t ht h0
    have h1 := (h t ht).2
    rw [h0, sub_self, mul_zero, mul_zero] at h1
    exact zero_ne_one h1
  have eH : ∀ x ∈ U.I, U.H x = 1 / (3 / 2 * (1 + w) * (x - t₀)) := by
    intro x hx
    have hx0 : x - t₀ ≠ 0 := sub_ne_zero.2 (hne x hx)
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) h1w) hx0)]
    exact (h x hx).2
  have eρ : ∀ x ∈ U.I, U.rho x = 3 / (8 * Real.pi * U.G) * U.H x ^ 2 := by
    intro x hx
    have h1 := U.friedmann₁ x hx
    rw [hK] at h1
    unfold FRWUniverse.H
    rw [h1]
    field_simp
    ring
  refine ⟨t₀, hne, fun s hs t ht => ⟨?_, ?_⟩⟩
  · have hs0 : s - t₀ ≠ 0 := sub_ne_zero.2 (hne s hs)
    have hr : ∀ u ∈ U.I, 0 < (u - t₀) / (s - t₀) := by
      intro u hu
      rcases lt_or_gt_of_ne (hne u hu) with h1 | h1 <;>
        rcases lt_or_gt_of_ne (hne s hs) with h2 | h2
      · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
      · exfalso; exact hne t₀ (U.I_conn.Icc_subset hu hs ⟨h1.le, h2.le⟩) rfl
      · exfalso; exact hne t₀ (U.I_conn.Icc_subset hs hu ⟨h2.le, h1.le⟩) rfl
      · exact div_pos (by linarith) (by linarith)
    have hg : ∀ u ∈ U.I, HasDerivAt
        (fun y => U.a y * ((y - t₀) / (s - t₀)) ^ (-(2 / (3 * (1 + w)))))
        (U.adot u * ((u - t₀) / (s - t₀)) ^ (-(2 / (3 * (1 + w)))) +
          U.a u * (1 / (s - t₀) * (-(2 / (3 * (1 + w)))) *
            ((u - t₀) / (s - t₀)) ^ (-(2 / (3 * (1 + w))) - 1))) u := by
      intro u hu
      have h1 : HasDerivAt (fun y => (y - t₀) / (s - t₀)) (1 / (s - t₀)) u :=
        ((hasDerivAt_id' u).sub_const t₀).div_const (s - t₀)
      exact (U.ha u hu).mul (h1.rpow_const (Or.inl (hr u hu).ne'))
    have hc := U.I_open.is_const_of_deriv_eq_zero
      (f := fun y => U.a y * ((y - t₀) / (s - t₀)) ^ (-(2 / (3 * (1 + w))))) U.I_conn
      (fun x hx => (hg x hx).differentiableAt.differentiableWithinAt)
      (fun u hu => by
        simp only [Pi.zero_apply]
        rw [(hg u hu).deriv, Real.rpow_sub_one (hr u hu).ne']
        have hu0 : u - t₀ ≠ 0 := sub_ne_zero.2 (hne u hu)
        have hHu := eH u hu
        unfold FRWUniverse.H at hHu
        have hau := (U.a_pos u hu).ne'
        have hadot : U.adot u = U.a u / (3 / 2 * (1 + w) * (u - t₀)) := by
          rw [div_eq_iff hau] at hHu; rw [hHu]; ring
        rw [hadot]
        generalize ((u - t₀) / (s - t₀)) ^ (-(2 / (3 * (1 + w)))) = R
        field_simp
        try ring) ht hs
    try simp only at hc
    rw [div_self hs0, Real.one_rpow, mul_one, Real.rpow_neg (hr t ht).le] at hc
    have hpos : 0 < ((t - t₀) / (s - t₀)) ^ (2 / (3 * (1 + w))) :=
      Real.rpow_pos_of_pos (hr t ht) _
    rw [← hc, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
  · have ht0 : t - t₀ ≠ 0 := sub_ne_zero.2 (hne t ht)
    have hs0 : s - t₀ ≠ 0 := sub_ne_zero.2 (hne s hs)
    rw [eρ t ht, eρ s hs, eH t ht, eH s hs]
    field_simp
    try ring

theorem W2c_FRWCosmology_power_law (G w : ℝ) (hG : 0 < G) (hw : w ≠ -1) :
    ∃ U : FRWUniverse, U.G = G ∧ U.K = 0 ∧ U.I = Set.Ioi 0 ∧ U.LinearEoS w ∧
      (∀ t ∈ U.I, 0 < U.rho t) ∧ (∀ t ∈ U.I, U.a t = t ^ (2 / (3 * (1 + w)))) := by
  have h1w : 1 + w ≠ 0 := by intro h0; apply hw; linarith
  have hπ := Real.pi_pos
  have hπ' := Real.pi_ne_zero
  have hG' := hG.ne'
  have hn : (2 / (3 * (1 + w)) : ℝ) ≠ 0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) h1w)
  set n : ℝ := 2 / (3 * (1 + w)) with hndef
  let rho : ℝ → ℝ := fun t => 3 * n ^ 2 / (8 * Real.pi * G) / t ^ 2
  have hrho : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt rho (deriv rho t) t := by
    intro t ht
    have ht0 : (t:ℝ) ≠ 0 := (Set.mem_Ioi.1 ht).ne'
    have h2 : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) t := by fun_prop
    exact ((differentiableAt_const _).div h2 (pow_ne_zero 2 ht0)).hasDerivAt
  have hf1 : ∀ t ∈ Set.Ioi (0:ℝ), (n * t ^ (n - 1) / t ^ n) ^ 2 =
      8 * Real.pi * G / 3 * rho t - 0 / (t ^ n) ^ 2 := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have htn : 0 < t ^ n := Real.rpow_pos_of_pos ht0 n
    show _ = 8 * Real.pi * G / 3 * (3 * n ^ 2 / (8 * Real.pi * G) / t ^ 2) - 0 / (t ^ n) ^ 2
    rw [Real.rpow_sub_one ht0.ne']
    field_simp
    try ring
  have hf2 : ∀ t ∈ Set.Ioi (0:ℝ), n * ((n - 1) * t ^ (n - 1 - 1)) / t ^ n -
      (n * t ^ (n - 1) / t ^ n) ^ 2 =
      -(4 * Real.pi * G) * (rho t + w * rho t) + 0 / (t ^ n) ^ 2 := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    have htn : 0 < t ^ n := Real.rpow_pos_of_pos ht0 n
    show _ = -(4 * Real.pi * G) * (3 * n ^ 2 / (8 * Real.pi * G) / t ^ 2 +
      w * (3 * n ^ 2 / (8 * Real.pi * G) / t ^ 2)) + 0 / (t ^ n) ^ 2
    simp only [Real.rpow_sub_one ht0.ne']
    generalize t ^ n = T at htn ⊢
    rw [hndef]
    field_simp
    ring
  refine ⟨⟨G, 0, Set.Ioi 0, fun t => t ^ n, fun t => n * t ^ (n - 1),
    fun t => n * ((n - 1) * t ^ (n - 1 - 1)), rho, deriv rho, fun t => w * rho t,
    isOpen_Ioi, isPreconnected_Ioi, fun t ht => Real.rpow_pos_of_pos ht n,
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl (Set.mem_Ioi.1 ht).ne'),
    fun t ht => (Real.hasDerivAt_rpow_const (Or.inl (Set.mem_Ioi.1 ht).ne')).const_mul n,
    hrho, hf1, hf2⟩,
    rfl, rfl, rfl, fun t _ => rfl, fun t ht => ?_, fun t _ => rfl⟩
  have ht0 : (0:ℝ) < t := ht
  show 0 < 3 * n ^ 2 / (8 * Real.pi * G) / t ^ 2
  have : 0 < n ^ 2 := lt_of_le_of_ne (sq_nonneg n) (Ne.symm (pow_ne_zero 2 hn))
  exact div_pos (div_pos (mul_pos (by norm_num) this) (by positivity)) (by positivity)

theorem solution (U : FRWUniverse) (hG : 0 < U.G) (hK : U.K = 0) (w : ℝ)
    (hw : w ≠ -1) (heos : U.LinearEoS w) (hrho : ∀ t ∈ U.I, 0 < U.rho t) :
    ∃ t₀ : ℝ, (∀ t ∈ U.I, t ≠ t₀) ∧
      ∀ s ∈ U.I, ∀ t ∈ U.I,
        U.a t = U.a s * ((t - t₀) / (s - t₀)) ^ (2 / (3 * (1 + w))) ∧
        U.rho t = U.rho s * ((s - t₀) / (t - t₀)) ^ 2 := by
  apply W2c_FRWCosmology_flat <;> assumption
