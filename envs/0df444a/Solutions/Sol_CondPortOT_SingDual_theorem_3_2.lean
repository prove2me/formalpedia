-- Prove2me | solution 1 for CondPortOT.SingDual.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T19:15:42.932247+00:00
-- url     : https://prove2.me/submissions/f31aefdb-8fd7-4543-8bae-048b22f408c9

import Mathlib
import Definitions.Def_CondPortOT_SingDual_Setting
open MeasureTheory

-- ===== SD_A.lean

namespace SDMainAux

/-- One-constraint Lagrangian duality on a convex set, via a separating line in `ℝ²`. -/
theorem sep2 {E : Type*} [AddCommGroup E] [Module ℝ E] (C : Set E) (hC : Convex ℝ C)
    (A V : E →ₗ[ℝ] ℝ) (ρ t : ℝ) (c0 : E) (hc0 : c0 ∈ C) (hA0 : A c0 < ρ)
    (hfeas : ∀ c ∈ C, A c < ρ → V c ≤ t) :
    ∃ l : ℝ, 0 ≤ l ∧ ∀ c ∈ C, V c + l * (ρ - A c) ≤ t := by
  set O : Set (ℝ × ℝ) := Set.Iio ρ ×ˢ Set.Ioi t with hO
  set K : Set (ℝ × ℝ) := (A.prod V) '' C with hK
  have hKc : Convex ℝ K := hC.linear_image _
  set B : Set (ℝ × ℝ) := {p | ∃ q ∈ K, q.1 ≤ p.1 ∧ p.2 ≤ q.2} with hB
  have hBc : Convex ℝ B := by
    intro p hp p' hp' a b ha hb hab
    obtain ⟨q, hq, h1, h2⟩ := hp
    obtain ⟨q', hq', h1', h2'⟩ := hp'
    refine ⟨a • q + b • q', hKc hq hq' ha hb hab, ?_, ?_⟩
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith
  have hOc : Convex ℝ O := (convex_Iio ρ).prod (convex_Ioi t)
  have hOo : IsOpen O := isOpen_Iio.prod isOpen_Ioi
  have hdisj : Disjoint O B := by
    rw [Set.disjoint_left]
    rintro p ⟨hp1, hp2⟩ ⟨q, ⟨c, hc, rfl⟩, h1, h2⟩
    simp only [Set.mem_Iio, Set.mem_Ioi] at hp1 hp2
    change A c ≤ p.1 at h1
    change p.2 ≤ V c at h2
    have := hfeas c hc (lt_of_le_of_lt h1 hp1)
    linarith
  obtain ⟨f, u, hfO, hfB⟩ := geometric_hahn_banach_open hOc hOo hBc hdisj
  set α := f (1, 0) with hα
  set β := f (0, 1) with hβ
  have hf : ∀ p : ℝ × ℝ, f p = α * p.1 + β * p.2 := by
    intro p
    have : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hα, hβ]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hKB : ∀ c ∈ C, (A c, V c) ∈ B := fun c hc => ⟨(A c, V c), ⟨c, hc, rfl⟩, le_rfl, le_rfl⟩
  have hu0 : u ≤ α * A c0 + β * V c0 := by
    have := hfB _ (hKB c0 hc0); rw [hf] at this; exact this
  have hαnn : 0 ≤ α := by
    by_contra hneg
    push_neg at hneg
    set s : ℝ := (α * A c0 + β * V c0 - u + 1) / (-α) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
    have hmem : (A c0 + s, V c0) ∈ B := ⟨(A c0, V c0), ⟨c0, hc0, rfl⟩, by simp; linarith, le_rfl⟩
    have := hfB _ hmem
    rw [hf] at this
    simp only at this
    have hαs : α * s = -(α * A c0 + β * V c0 - u + 1) := by
      have : α ≠ 0 := by linarith
      rw [hs]; field_simp
    nlinarith
  have hβnp : β ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    set s : ℝ := (α * A c0 + β * V c0 - u + 1) / β with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
    have hmem : (A c0, V c0 - s) ∈ B := ⟨(A c0, V c0), ⟨c0, hc0, rfl⟩, le_rfl, by simp; linarith⟩
    have := hfB _ hmem
    rw [hf] at this
    simp only at this
    have hβs : β * s = (α * A c0 + β * V c0 - u + 1) := by
      have : β ≠ 0 := by linarith
      rw [hs]; field_simp
    nlinarith
  have hOmem : ∀ η : ℝ, 0 < η → ∀ w : ℝ, t < w → α * (ρ - η) + β * w < u := by
    intro η hη w hw
    have := hfO (ρ - η, w) ⟨by simp; linarith, by simpa using hw⟩
    rwa [hf] at this
  have hβneg : β < 0 := by
    rcases hβnp.lt_or_eq with h | h
    · exact h
    exfalso
    rcases hαnn.lt_or_eq with hα0 | hα0
    · have := hOmem ((ρ - A c0) / 2) (by linarith) (t + 1) (by linarith)
      rw [h] at this hu0
      nlinarith
    · have := hOmem 1 one_pos (t + 1) (by linarith)
      rw [h, ← hα0] at this
      rw [h, ← hα0] at hu0
      linarith
  refine ⟨α / (-β), div_nonneg hαnn (by linarith), fun c hc => ?_⟩
  have hcu : u ≤ α * A c + β * V c := by
    have := hfB _ (hKB c hc); rw [hf] at this; exact this
  have key : α * ρ + β * t ≤ α * A c + β * V c := by
    by_contra hlt
    push_neg at hlt
    set d := α * ρ + β * t - (α * A c + β * V c) with hd
    have hd0 : 0 < d := by linarith
    set η := d / (α - β + 1) with hη
    have hη0 : 0 < η := div_pos hd0 (by linarith)
    have h1 := hOmem η hη0 (t + η) (by linarith)
    have hηm : η * (α - β + 1) = d := by
      have : α - β + 1 ≠ 0 := by linarith
      rw [hη]; field_simp
    nlinarith
  have hnb : 0 < -β := by linarith
  have h2 : α / -β * (ρ - A c) ≤ t - V c := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hnb]
    nlinarith
  linarith

end SDMainAux

-- ===== SD_B.lean

namespace SDMainAux

/-- The "top-`Nε` average" identity: `inf_l {Nεl + Σ (Gᵢ - l)⁺}` is attained by an `ε`-quantile
`l` and equals `Σ υᵢ Gᵢ` for a weight vector `υ ∈ [0,1]ᴺ` with `Σ υᵢ = Nε`. -/
theorem cvar {N : ℕ} (hN : 0 < N) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (G : Fin N → ℝ) :
    ∃ l2 : ℝ, ∃ υ : Fin N → ℝ, (∀ i, 0 ≤ υ i ∧ υ i ≤ 1) ∧ ∑ i, υ i = N * ε ∧
      N * ε * l2 + ∑ i, max (G i - l2) 0 = ∑ i, υ i * G i := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set cnt : ℝ → ℕ := fun l => (Finset.univ.filter (fun i => l ≤ G i)).card with hcnt
  set J := Finset.univ.filter (fun j => (N : ℝ) * ε ≤ cnt (G j)) with hJ
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ G hne
  have hJne : J.Nonempty := by
    refine ⟨j0, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    have : cnt (G j0) = N := by
      simp only [hcnt]
      rw [Finset.filter_true_of_mem (fun i _ => hj0 i (Finset.mem_univ i)), Finset.card_univ,
        Fintype.card_fin]
    rw [this]
    nlinarith
  obtain ⟨js, hjsJ, hjs⟩ := Finset.exists_max_image J G hJne
  set l2 := G js with hl2
  have hE : (N : ℝ) * ε ≤ cnt l2 := (Finset.mem_filter.1 hjsJ).2
  set Sg := Finset.univ.filter (fun i => l2 < G i) with hSg
  set Eq := Finset.univ.filter (fun i => G i = l2) with hEq
  have hsplit : cnt l2 = Sg.card + Eq.card := by
    simp only [hcnt]
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hSg, hEq]
      constructor
      · intro h; rcases h.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h.symm
      · rintro (h | h)
        · exact h.le
        · exact h.ge
    · rw [Finset.disjoint_left]
      intro i hi hi'
      simp only [Finset.mem_filter, hSg, hEq] at hi hi'
      linarith [hi.2, hi'.2]
  have hS : (Sg.card : ℝ) ≤ N * ε := by
    by_contra h
    push_neg at h
    have hSne : Sg.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < Sg.card := lt_trans (by positivity) h
      exact_mod_cast this
    obtain ⟨k, hkS, hk⟩ := Finset.exists_min_image Sg G hSne
    have hsub : Sg ⊆ Finset.univ.filter (fun i => G k ≤ G i) := by
      intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hk i hi⟩
    have hkJ : k ∈ J := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      have := Finset.card_le_card hsub
      have h2 : (Sg.card : ℝ) ≤ cnt (G k) := by exact_mod_cast this
      linarith
    have := hjs k hkJ
    have hk2 : l2 < G k := (Finset.mem_filter.1 hkS).2
    linarith
  have hEqpos : (0 : ℝ) < Eq.card := by
    have : js ∈ Eq := Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
    exact_mod_cast Finset.card_pos.2 ⟨js, this⟩
  set θ : ℝ := ((N : ℝ) * ε - Sg.card) / Eq.card with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hEqpos.le
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hEqpos]
    have : ((cnt l2 : ℕ) : ℝ) = Sg.card + Eq.card := by rw [hsplit]; push_cast; ring
    linarith
  have hθE : θ * Eq.card = N * ε - Sg.card := by
    rw [hθ]; field_simp
  refine ⟨l2, fun i => (if l2 < G i then 1 else 0) + (if G i = l2 then θ else 0), ?_, ?_, ?_⟩
  · intro i
    by_cases h1 : l2 < G i
    · have h2 : ¬ G i = l2 := by intro h; linarith
      simp [h1, h2]
    · by_cases h2 : G i = l2
      · simp [h1, h2, hθ0, hθ1]
      · simp [h1, h2]
  · rw [Finset.sum_add_distrib, Finset.sum_boole, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul]
    rw [← hSg, ← hEq]
    linarith [hθE]
  · have h1 : ∑ i, max (G i - l2) 0 = ∑ i ∈ Sg, (G i - l2) := by
      rw [hSg, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : l2 < G i
      · rw [if_pos h, max_eq_left (by linarith)]
      · rw [if_neg h, max_eq_right (by linarith)]
    have h2 : ∑ i, ((if l2 < G i then 1 else 0) + (if G i = l2 then θ else 0)) * G i =
        ∑ i ∈ Sg, G i + θ * Eq.card * l2 := by
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter, ← Finset.sum_filter, ← hSg, ← hEq]
      rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2] :
        ∀ i ∈ Eq, θ * G i = θ * l2), Finset.sum_const, nsmul_eq_mul]
      ring
    rw [h1, h2, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hθE]
    ring

end SDMainAux

-- ===== SD_C.lean

namespace SDMainAux

section Setup
variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The linear functional `ν ↦ Σ_p ν(p) w(p)` on finitely supported weights. -/
noncomputable abbrev Lam {α : Type*} (w : α → ℝ) : (α →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ w

lemma Lam_apply {α : Type*} (w : α → ℝ) (ν : α →₀ ℝ) :
    Lam w ν = ∑ p ∈ ν.support, ν p * w p := by
  simp [Lam, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

lemma DY_self (DX : X → X → ℝ) (DY : Y → Y → ℝ) (x0 : X) {N : ℕ} (xh : Fin N → X)
    (hA : CondPortOT.SingDual.Assumption24 DX DY x0 0 xh) (y : Y) : DY y y = 0 := by
  have h := (hA.zero_iff x0 x0 y y).2 rfl
  linarith [hA.nonneg_X x0 x0, hA.nonneg_Y y y]

lemma DX_self (DX : X → X → ℝ) (DY : Y → Y → ℝ) (x0 : X) {N : ℕ} (xh : Fin N → X)
    (hA : CondPortOT.SingDual.Assumption24 DX DY x0 0 xh) (y : Y) (x : X) : DX x x = 0 := by
  have h := (hA.zero_iff x x y y).2 rfl
  linarith [hA.nonneg_X x x, hA.nonneg_Y y y]

lemma mem_F (DX : X → X → ℝ) (DY : Y → Y → ℝ) (x0 : X) {N : ℕ} (xh : Fin N → X)
    (hA : CondPortOT.SingDual.Assumption24 DX DY x0 0 xh) (w : X × Y) :
    w ∈ CondPortOT.SingUninf.fiber (Y := Y) DX x0 0 ↔ w.1 = x0 := by
  simp only [CondPortOT.SingUninf.fiber, CondPortOT.SingUninf.nbhd, Set.mem_prod,
    Set.mem_setOf_eq, Set.mem_univ, and_true]
  constructor
  · intro h
    have h0 : DX w.1 x0 + DY w.2 w.2 = 0 := by
      rw [DY_self DX DY x0 xh hA]; linarith [hA.nonneg_X w.1 x0]
    have := (hA.zero_iff w.1 x0 w.2 w.2).1 h0
    exact (Prod.mk.inj this).1
  · intro h; rw [h, DX_self DX DY x0 xh hA w.2]

lemma F_meas (DX : X → X → ℝ) (DY : Y → Y → ℝ) (x0 : X) {N : ℕ} (xh : Fin N → X)
    (hA : CondPortOT.SingDual.Assumption24 DX DY x0 0 xh) :
    MeasurableSet (CondPortOT.SingUninf.fiber (Y := Y) DX x0 0) := by
  have hc : Continuous fun x : X => DX x x0 := hA.cont_X.comp (continuous_id.prodMk continuous_const)
  have : IsClosed (CondPortOT.SingUninf.nbhd DX x0 0) := isClosed_le hc continuous_const
  exact this.measurableSet.prod MeasurableSet.univ

lemma ofReal_max0 (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]


lemma sum_mass {N : ℕ} {Y : Type*} (ν : (Fin N × Y) →₀ ℝ) :
    ∑ i, Lam (fun p : Fin N × Y => if p.1 = i then (1 : ℝ) else 0) ν = ∑ p ∈ ν.support, ν p := by
  classical
  simp only [Lam_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum]
  simp

lemma mass_eq {N : ℕ} {Y : Type*} (ν : (Fin N × Y) →₀ ℝ) (i : Fin N) :
    Lam (fun p : Fin N × Y => if p.1 = i then (1 : ℝ) else 0) ν =
      ∑ p ∈ ν.support with p.1 = i, ν p := by
  classical
  rw [Lam_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

/-- Building a feasible measure from finitely supported fiber weights `ν`. -/
theorem qcon (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X)
    (yh : Fin N → Y) (x0 : X) (hA : CondPortOT.SingDual.Assumption24 DX DY x0 0 xh)
    (hH1 : CondPortOT.SingUninf.NotIsolated DX x0) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ρ : ℝ)
    (L : Y → ℝ) (ν : (Fin N × Y) →₀ ℝ) (hν0 : ∀ p, 0 ≤ ν p)
    (hν1 : ∀ i, Lam (fun p : Fin N × Y => if p.1 = i then (1 : ℝ) else 0) ν ≤ 1)
    (hνs : ∑ i, Lam (fun p : Fin N × Y => if p.1 = i then (1 : ℝ) else 0) ν = N * ε)
    (ha : (N : ℝ)⁻¹ * Lam (fun p : Fin N × Y => DX x0 (xh p.1) + DY p.2 (yh p.1)) ν < ρ) :
    ∃ Q : Measure (X × Y), CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ∧
      ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 0) ∧
      CondPortOT.SingUninf.condExp Q (CondPortOT.SingUninf.fiber DX x0 0) L =
        ((((N : ℝ) * ε)⁻¹ * Lam (fun p : Fin N × Y => L p.2) ν : ℝ) : EReal) := by
  classical
  set F := CondPortOT.SingUninf.fiber (Y := Y) DX x0 0 with hF
  have hFm : MeasurableSet F := F_meas DX DY x0 xh hA
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set m : Fin N → ℝ := fun i => Lam (fun p : Fin N × Y => if p.1 = i then (1 : ℝ) else 0) ν
    with hm
  have hm_eq : ∀ i, m i = ∑ p ∈ ν.support with p.1 = i, ν p := fun i => mass_eq ν i
  have hm0 : ∀ i, 0 ≤ m i := fun i => by
    rw [hm_eq]; exact Finset.sum_nonneg fun p _ => hν0 p
  have hsumν : ∑ p ∈ ν.support, ν p = N * ε := by rw [← sum_mass ν]; exact hνs
  set a := (N : ℝ)⁻¹ * Lam (fun p : Fin N × Y => DX x0 (xh p.1) + DY p.2 (yh p.1)) ν with ha_def
  set r := ρ - a with hr
  have hr0 : 0 < r := by linarith
  obtain ⟨x1, hx1ne, hx1⟩ := hH1 r hr0
  set x' : Fin N → X := fun i => if xh i = x0 then x1 else xh i with hx'
  have hx'ne : ∀ i, x' i ≠ x0 := by
    intro i; simp only [hx']; split_ifs with h
    · exact hx1ne
    · exact h
  have hx'c : ∀ i, DX (x' i) (xh i) ≤ r := by
    intro i; simp only [hx']; split_ifs with h
    · rw [h]; exact hx1
    · rw [DX_self DX DY x0 xh hA (yh i)]; exact hr0.le
  have hx'F : ∀ i, (x' i, yh i) ∉ F := fun i h => hx'ne i ((mem_F DX DY x0 xh hA _).1 h)
  have hx0F : ∀ y : Y, (x0, y) ∈ F := fun y => (mem_F DX DY x0 xh hA _).2 rfl
  set c : Fin N × Y → ℝ := fun p => ν p / N with hc
  set d : Fin N → ℝ := fun i => (1 - m i) / N with hd
  have hc0 : ∀ p, 0 ≤ c p := fun p => div_nonneg (hν0 p) hNpos.le
  have hd0 : ∀ i, 0 ≤ d i := fun i => div_nonneg (by linarith [hν1 i]) hNpos.le
  set z : Fin N → X × Y := fun i => (xh i, yh i) with hz
  set π : Measure ((X × Y) × (X × Y)) :=
    (∑ p ∈ ν.support, ENNReal.ofReal (c p) • Measure.dirac ((x0, p.2), z p.1)) +
      ∑ i, ENNReal.ofReal (d i) • Measure.dirac ((x' i, yh i), z i) with hπ
  set Q : Measure (X × Y) :=
    (∑ p ∈ ν.support, ENNReal.ofReal (c p) • Measure.dirac (x0, p.2)) +
      ∑ i, ENNReal.ofReal (d i) • Measure.dirac (x' i, yh i) with hQ
  have hlinπ : ∀ g : (X × Y) × (X × Y) → ENNReal, ∫⁻ w, g w ∂π =
      ∑ p ∈ ν.support, ENNReal.ofReal (c p) * g ((x0, p.2), z p.1) +
        ∑ i, ENNReal.ofReal (d i) * g ((x' i, yh i), z i) := by
    intro g
    simp only [hπ, lintegral_add_measure, lintegral_finsetSum_measure, lintegral_smul_measure,
      lintegral_dirac, smul_eq_mul]
  have hlinQ : ∀ g : X × Y → ENNReal, ∫⁻ w, g w ∂Q =
      ∑ p ∈ ν.support, ENNReal.ofReal (c p) * g (x0, p.2) +
        ∑ i, ENNReal.ofReal (d i) * g (x' i, yh i) := by
    intro g
    simp only [hQ, lintegral_add_measure, lintegral_finsetSum_measure, lintegral_smul_measure,
      lintegral_dirac, smul_eq_mul]
  have hrestr : ∀ g : X × Y → ENNReal, ∫⁻ w, g w ∂(Q.restrict F) =
      ∑ p ∈ ν.support, ENNReal.ofReal (c p) * g (x0, p.2) := by
    intro g
    rw [← lintegral_indicator hFm, hlinQ]
    have h2 : ∑ i, ENNReal.ofReal (d i) * F.indicator g (x' i, yh i) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [Set.indicator_of_notMem (hx'F i), mul_zero]
    rw [h2, add_zero]
    exact Finset.sum_congr rfl fun p _ => by rw [Set.indicator_of_mem (hx0F p.2)]
  have hsumc : ∑ p ∈ ν.support, c p = ε := by
    simp only [hc]; rw [← Finset.sum_div, hsumν]; field_simp
  have hQF : Q F = ENNReal.ofReal ε := by
    rw [← lintegral_indicator_one hFm]
    have := hrestr (fun _ => 1)
    rw [lintegral_indicator_one hFm] at *
    rw [← Measure.restrict_apply_univ, ← lintegral_one, this]
    simp only [mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => hc0 p, hsumc]
  -- marginals
  have hfst : π.map Prod.fst = Q := by
    simp only [hπ, hQ]
    rw [Measure.map_add _ _ measurable_fst, Measure.map_finset_sum measurable_fst.aemeasurable,
      Measure.map_finset_sum measurable_fst.aemeasurable]
    simp only [Measure.map_smul, Measure.map_dirac' measurable_fst]
  have hregroup : ∀ g : Fin N → ENNReal, ∑ p ∈ ν.support, ENNReal.ofReal (c p) * g p.1 =
      ∑ i, ENNReal.ofReal (m i / N) * g i := by
    intro g
    rw [← Finset.sum_fiberwise_of_maps_to (s := ν.support) (t := Finset.univ) (g := Prod.fst)
      (fun p _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2] :
      ∀ p ∈ Finset.filter (fun p : Fin N × Y => p.1 = i) ν.support, ENNReal.ofReal (c p) * g p.1 = ENNReal.ofReal (c p) * g i),
      ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun p _ => hc0 p, hm_eq i]
    simp only [hc]; rw [Finset.sum_div]
  have hNinv : ENNReal.ofReal ((N : ℝ)⁻¹) = (N : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  have hmd : ∀ i, ENNReal.ofReal (m i / N) + ENNReal.ofReal (d i) = (N : ENNReal)⁻¹ := by
    intro i
    rw [← ENNReal.ofReal_add (div_nonneg (hm0 i) hNpos.le) (hd0 i), ← hNinv]
    congr 1
    simp only [hd]; field_simp; ring
  have hsnd : π.map Prod.snd = CondPortOT.SingUninf.empirical xh yh := by
    ext B hB
    rw [Measure.map_apply measurable_snd hB, ← lintegral_indicator_one (hB.preimage measurable_snd),
      hlinπ]
    simp only [CondPortOT.SingUninf.empirical, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
    have e1 : ∀ (u : X × Y) (i : Fin N), (Prod.snd ⁻¹' B).indicator (1 : (X × Y) × (X × Y) → ENNReal)
        (u, z i) = B.indicator 1 (z i) := by
      intro u i; simp [Set.indicator_apply]
    simp only [e1]
    rw [hregroup (fun i => B.indicator 1 (z i)), ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_mul, hmd i]
  have hπuniv : π Set.univ = 1 := by
    have := congrArg (fun μ : Measure (X × Y) => μ Set.univ) hsnd
    simp only [Measure.map_apply measurable_snd MeasurableSet.univ, Set.preimage_univ] at this
    rw [this]
    simp only [CondPortOT.SingUninf.empirical, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top _)
  have hπprob : IsProbabilityMeasure π := ⟨hπuniv⟩
  have hQprob : IsProbabilityMeasure Q := by
    rw [← hfst]; exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  refine ⟨Q, ⟨hQprob, ?_⟩, hQF.ge, ?_⟩
  · -- transport cost
    unfold RWPI.SqrtLasso.transportCost
    refine iInf₂_le_of_le π ⟨hπprob, hfst, hsnd⟩ ?_
    rw [hlinπ]
    simp only [CondPortOT.SingUninf.groundCost, hz, DY_self DX DY x0 xh hA, add_zero]
    have h1 : ∑ p ∈ ν.support, ENNReal.ofReal (c p) * ENNReal.ofReal (DX x0 (xh p.1) + DY p.2 (yh p.1))
        = ENNReal.ofReal a := by
      rw [Finset.sum_congr rfl fun p _ => (ENNReal.ofReal_mul (hc0 p)).symm,
        ← ENNReal.ofReal_sum_of_nonneg fun p _ => mul_nonneg (hc0 p)
          (add_nonneg (hA.nonneg_X _ _) (hA.nonneg_Y _ _))]
      congr 1
      rw [ha_def, Lam_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [hc]; ring
    have h2 : ∑ i, ENNReal.ofReal (d i) * ENNReal.ofReal (DX (x' i) (xh i)) ≤ ENNReal.ofReal r := by
      calc ∑ i, ENNReal.ofReal (d i) * ENNReal.ofReal (DX (x' i) (xh i))
          ≤ ∑ i, ENNReal.ofReal (d i * r) := Finset.sum_le_sum fun i _ => by
            rw [← ENNReal.ofReal_mul (hd0 i)]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hx'c i) (hd0 i))
        _ = ENNReal.ofReal (∑ i, d i * r) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hd0 i) hr0.le).symm
        _ ≤ ENNReal.ofReal r := by
            apply ENNReal.ofReal_le_ofReal
            rw [← Finset.sum_mul]
            have : ∑ i, d i = 1 - ε := by
              simp only [hd]
              rw [← Finset.sum_div, Finset.sum_sub_distrib, hνs]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
              field_simp
            rw [this]; nlinarith
    calc _ ≤ ENNReal.ofReal a + ENNReal.ofReal r := by rw [h1]; gcongr
      _ = ENNReal.ofReal ρ := by
          rw [← ENNReal.ofReal_add (by
            rw [ha_def]; exact mul_nonneg (inv_nonneg.2 hNpos.le) (by
              rw [Lam_apply]; exact Finset.sum_nonneg fun p _ => mul_nonneg (hν0 p)
                (add_nonneg (hA.nonneg_X _ _) (hA.nonneg_Y _ _)))) hr0.le]
          congr 1; rw [hr]; ring
  · -- conditional expectation
    unfold CondPortOT.SingUninf.condExp ModelRiskOT.Duality.extIntegral
    have e1 : (fun p : X × Y => ((L p.2 : ℝ) : EReal).toENNReal) = fun p => ENNReal.ofReal (L p.2) := by
      funext p; rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    have e2 : (fun p : X × Y => (-((L p.2 : ℝ) : EReal)).toENNReal) =
        fun p => ENNReal.ofReal (-L p.2) := by
      funext p
      rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
    rw [e1, e2, hrestr, hrestr, hQF, ENNReal.toReal_ofReal hε0.le]
    have hpos : ∀ u : ℝ, ∑ p ∈ ν.support, ENNReal.ofReal (c p) * ENNReal.ofReal (u * L p.2) =
        ENNReal.ofReal (∑ p ∈ ν.support, c p * max (u * L p.2) 0) := by
      intro u
      rw [ENNReal.ofReal_sum_of_nonneg fun p _ => mul_nonneg (hc0 p) (le_max_right _ _)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [ENNReal.ofReal_mul (hc0 p), ← ofReal_max0]
    have hp1 := hpos 1
    have hm1 := hpos (-1)
    simp only [one_mul, neg_one_mul] at hp1 hm1
    rw [hp1, hm1, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal]
    rw [max_eq_left (Finset.sum_nonneg fun p _ => mul_nonneg (hc0 p) (le_max_right _ _)),
      max_eq_left (Finset.sum_nonneg fun p _ => mul_nonneg (hc0 p) (le_max_right _ _)),
      ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_eq_coe_iff, ← Finset.sum_sub_distrib, Lam_apply,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hmx : max (L p.2) 0 - max (-L p.2) 0 = L p.2 := by
      rcases le_total 0 (L p.2) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    rw [← mul_sub, hmx]
    simp only [hc]
    field_simp

end Setup

end SDMainAux

-- ===== SD_Dc.lean

namespace SDMainAux
/-- regrouping a sum over samples by distinct atoms. -/
lemma regroup {Ω : Type*} [DecidableEq Ω] {N : ℕ} (z : Fin N → Ω) (F : Ω → ENNReal) :
    ∑ a ∈ Finset.univ.image z, F a =
      ∑ i, ((Finset.univ.filter fun j => z j = z i).card : ENNReal)⁻¹ * F (z i) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image z) (g := z)
    (fun i _ => Finset.mem_image_of_mem z (Finset.mem_univ i))]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨i0, -, rfl⟩ := Finset.mem_image.1 ha
  have hcard : ∀ i ∈ Finset.univ.filter (fun i => z i = z i0),
      ((Finset.univ.filter fun j => z j = z i).card : ENNReal)⁻¹ * F (z i) =
      ((Finset.univ.filter fun j => z j = z i0).card : ENNReal)⁻¹ * F (z i0) := by
    intro i hi
    rw [(Finset.mem_filter.1 hi).2]
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel, one_mul]
  · have : i0 ∈ Finset.univ.filter (fun j => z j = z i0) := by simp
    exact_mod_cast (Finset.card_pos.2 ⟨i0, this⟩).ne'
  · exact ENNReal.natCast_ne_top _

/-- Decomposition of a coupling whose second marginal is an empirical measure. -/
theorem decomp {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {N : ℕ}
    (z : Fin N → Ω) (π : Measure (Ω × Ω))
    (hπ : π.map Prod.snd = (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (z i)) :
    ∃ πi : Fin N → Measure Ω, (∀ i, πi i Set.univ = (N : ENNReal)⁻¹) ∧
      (∀ g : Ω × Ω → ENNReal, Measurable g →
        ∫⁻ w, g w ∂π = ∑ i, ∫⁻ x, g (x, z i) ∂(πi i)) := by
  classical
  set m : Fin N → ENNReal := fun i => ((Finset.univ.filter fun j => z j = z i).card : ENNReal)
    with hm
  have hm0 : ∀ i, m i ≠ 0 := by
    intro i
    have : i ∈ Finset.univ.filter (fun j => z j = z i) := by simp
    rw [hm]
    exact Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨i, this⟩).ne'
  have hmt : ∀ i, m i ≠ ⊤ := fun i => ENNReal.natCast_ne_top _
  set π' : Ω → Measure Ω := fun a => (π.restrict (Set.univ ×ˢ {a})).map Prod.fst with hπ'
  refine ⟨fun i => (m i)⁻¹ • π' (z i), ?_, ?_⟩
  · intro i
    have h1 : π (Set.univ ×ˢ {z i}) = (N : ENNReal)⁻¹ * m i := by
      have := congrArg (fun μ : Measure Ω => μ {z i}) hπ
      rw [Measure.map_apply measurable_snd (measurableSet_singleton _)] at this
      have hpre : Prod.snd ⁻¹' ({z i} : Set Ω) = (Set.univ ×ˢ {z i} : Set (Ω × Ω)) := by
        ext w; simp
      rw [hpre] at this
      rw [this, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
      congr 1
      simp only [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator_apply,
        Set.mem_singleton_iff, Pi.one_apply]
      rw [Finset.sum_boole]
    simp only [Measure.smul_apply, smul_eq_mul, hπ']
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, h1, ← mul_assoc,
      mul_comm (m i)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (hm0 i) (hmt i), mul_one]
  · intro g hg
    set S : Finset Ω := Finset.univ.image z with hS
    -- π is concentrated on `univ ×ˢ S`
    have hconc : π (Set.univ ×ˢ (↑S : Set Ω) : Set (Ω × Ω))ᶜ = 0 := by
      have hmeasS : MeasurableSet (↑S : Set Ω) := S.finite_toSet.measurableSet
      have hpre : (Set.univ ×ˢ (↑S : Set Ω) : Set (Ω × Ω))ᶜ = Prod.snd ⁻¹' ((↑S : Set Ω)ᶜ) := by
        ext w; simp
      rw [hpre, ← Measure.map_apply measurable_snd hmeasS.compl, hπ, Measure.smul_apply,
        Measure.coe_finsetSum, Finset.sum_apply]
      rw [Finset.sum_eq_zero fun i _ => ?_, smul_zero]
      rw [Measure.dirac_apply' _ hmeasS.compl, Set.indicator_of_notMem]
      simp [hS]
    have h1 : ∫⁻ w, g w ∂π = ∫⁻ w in Set.univ ×ˢ (↑S : Set Ω), g w ∂π := by
      rw [← lintegral_add_compl _ (MeasurableSet.univ.prod S.finite_toSet.measurableSet),
        setLIntegral_measure_zero _ _ hconc, add_zero]
    have hunion : (Set.univ ×ˢ (↑S : Set Ω) : Set (Ω × Ω)) =
        ⋃ a ∈ S, (Set.univ ×ˢ ({a} : Set Ω) : Set (Ω × Ω)) := by
      ext w; simp
    rw [h1, hunion, lintegral_biUnion_finset]
    rotate_left
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Set.disjoint_prod]
      right
      simpa using hab
    · intro a _
      exact MeasurableSet.univ.prod (measurableSet_singleton a)
    have h2 : ∀ a, ∫⁻ w in Set.univ ×ˢ ({a} : Set Ω), g w ∂π = ∫⁻ x, g (x, a) ∂(π' a) := by
      intro a
      have hgm : Measurable fun x : Ω => g (x, a) := hg.comp (measurable_id.prodMk measurable_const)
      show _ = ∫⁻ x, g (x, a) ∂((π.restrict (Set.univ ×ˢ {a})).map Prod.fst)
      rw [lintegral_map hgm measurable_fst]
      refine setLIntegral_congr_fun (MeasurableSet.univ.prod (measurableSet_singleton a)) ?_
      intro w hw
      have : w.2 = a := by simpa using hw.2
      simp [← this]
    simp_rw [h2]
    rw [regroup z (fun a => ∫⁻ x, g (x, a) ∂(π' a))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_smul_measure, smul_eq_mul]



end SDMainAux

-- ===== SD_D.lean

namespace SDMainAux

section W
variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

lemma gc_meas (DX : X → X → ℝ) (DY : Y → Y → ℝ)
    (hDXc : Continuous fun p : X × X => DX p.1 p.2) (hDYc : Continuous fun p : Y × Y => DY p.1 p.2) :
    Measurable fun w : (X × Y) × (X × Y) => CondPortOT.SingUninf.groundCost DX DY w.1 w.2 := by
  unfold CondPortOT.SingUninf.groundCost
  refine ENNReal.measurable_ofReal.comp (Measurable.add ?_ ?_)
  · exact hDXc.measurable.comp (measurable_fst.fst.prodMk measurable_snd.fst)
  · exact hDYc.measurable.comp (measurable_fst.snd.prodMk measurable_snd.snd)

lemma pt_real (u s C l1 l2 : ℝ) (hl1 : 0 ≤ l1) (hC : 0 ≤ C) (hs : 0 ≤ s)
    (h : u - C * l1 - l2 ≤ s) :
    max u 0 + max (-l2) 0 ≤ max (-u) 0 + s + l1 * C + max l2 0 := by
  have hlc : 0 ≤ l1 * C := mul_nonneg hl1 hC
  rcases le_total 0 u with hu | hu
  · rw [max_eq_left hu, max_eq_right (by linarith : -u ≤ 0)]
    rcases le_total 0 l2 with hl | hl
    · rw [max_eq_right (by linarith : -l2 ≤ 0), max_eq_left hl]; nlinarith
    · rw [max_eq_left (by linarith : 0 ≤ -l2), max_eq_right hl]; nlinarith
  · rw [max_eq_right hu, max_eq_left (by linarith : 0 ≤ -u)]
    rcases le_total 0 l2 with hl | hl
    · rw [max_eq_right (by linarith : -l2 ≤ 0), max_eq_left hl]; nlinarith
    · rw [max_eq_left (by linarith : 0 ≤ -l2), max_eq_right hl]; nlinarith

/-- Weak duality against a fixed coupling of cost at most `C`. -/
theorem weak_core (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X)
    (yh : Fin N → Y) (x0 : X) (hA : CondPortOT.SingDual.Assumption24 DX DY x0 0 xh)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (L : Y → ℝ) (hL : Measurable L) (l1 l2 : ℝ)
    (hl1 : 0 ≤ l1) (s : Fin N → ℝ) (hs0 : ∀ i, 0 ≤ s i)
    (hs : ∀ i y, ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 - l2 ≤ s i)
    (Q : Measure (X × Y)) [IsProbabilityMeasure Q]
    (hQF : ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 0))
    (π : Measure ((X × Y) × (X × Y))) (hπ1 : π.map Prod.fst = Q)
    (hπ2 : π.map Prod.snd = CondPortOT.SingUninf.empirical xh yh) (C : ℝ) (hC0 : 0 ≤ C)
    (hπC : ∫⁻ w, CondPortOT.SingUninf.groundCost DX DY w.1 w.2 ∂π ≤ ENNReal.ofReal C) :
    CondPortOT.SingUninf.condExp Q (CondPortOT.SingUninf.fiber DX x0 0) L ≤
      ((C * l1 + ε * l2 + (N : ℝ)⁻¹ * ∑ i, s i : ℝ) : EReal) := by
  classical
  set F := CondPortOT.SingUninf.fiber (Y := Y) DX x0 0 with hF
  have hFm : MeasurableSet F := F_meas DX DY x0 xh hA
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set z : Fin N → X × Y := fun i => (xh i, yh i) with hz
  obtain ⟨πi, hmass, hint⟩ := decomp z π (by rw [hπ2]; rfl)
  have hQint : ∀ h : X × Y → ENNReal, Measurable h →
      ∫⁻ x, h x ∂(Q.restrict F) = ∑ i, ∫⁻ x, F.indicator h x ∂(πi i) := by
    intro h hh
    rw [← lintegral_indicator hFm, ← hπ1, lintegral_map (hh.indicator hFm) measurable_fst]
    exact hint (fun w => F.indicator h w.1) ((hh.indicator hFm).comp measurable_fst)
  set cost := fun w : (X × Y) × (X × Y) => CondPortOT.SingUninf.groundCost DX DY w.1 w.2
    with hcost
  have hcm : Measurable cost := gc_meas DX DY hA.cont_X hA.cont_Y
  have hcost_sum : ∫⁻ w, cost w ∂π = ∑ i, ∫⁻ x, cost (x, z i) ∂(πi i) := hint _ hcm
  have hLm : Measurable fun x : X × Y => L x.2 := hL.comp measurable_snd
  set fp : X × Y → ENNReal := fun x => ENNReal.ofReal (ε⁻¹ * L x.2) with hfp
  set fm : X × Y → ENNReal := fun x => ENNReal.ofReal (-(ε⁻¹ * L x.2)) with hfm
  have hfpm : Measurable fp := ENNReal.measurable_ofReal.comp (measurable_const.mul hLm)
  have hfmm : Measurable fm := ENNReal.measurable_ofReal.comp (measurable_const.mul hLm).neg
  -- the pointwise inequality, integrated against each `πᵢ`
  have hpt : ∀ i, ∫⁻ x, F.indicator fp x ∂(πi i) + ENNReal.ofReal (-l2) * πi i F ≤
      ∫⁻ x, F.indicator fm x ∂(πi i) + ENNReal.ofReal (s i) * πi i F +
        ENNReal.ofReal l1 * ∫⁻ x, cost (x, z i) ∂(πi i) + ENNReal.ofReal l2 * πi i F := by
    intro i
    have hci : Measurable fun x : X × Y => cost (x, z i) :=
      hcm.comp (measurable_id.prodMk measurable_const)
    have hmF : ∀ c : ENNReal, Measurable (F.indicator fun _ : X × Y => c) :=
      fun c => measurable_const.indicator hFm
    calc ∫⁻ x, F.indicator fp x ∂(πi i) + ENNReal.ofReal (-l2) * πi i F
        = ∫⁻ x, (F.indicator fp x + F.indicator (fun _ => ENNReal.ofReal (-l2)) x) ∂(πi i) := by
          rw [lintegral_add_left (hfpm.indicator hFm), lintegral_indicator_const hFm]
      _ ≤ ∫⁻ x, (F.indicator fm x + F.indicator (fun _ => ENNReal.ofReal (s i)) x +
            ENNReal.ofReal l1 * cost (x, z i) + F.indicator (fun _ => ENNReal.ofReal l2) x) ∂(πi i) :=
          ?_
      _ = _ := by
          have m3 : Measurable (fun x => F.indicator fm x +
              F.indicator (fun _ => ENNReal.ofReal (s i)) x + ENNReal.ofReal l1 * cost (x, z i)) :=
            ((hfmm.indicator hFm).add (hmF _)).add (measurable_const.mul hci)
          have m2 : Measurable (fun x => F.indicator fm x +
              F.indicator (fun _ => ENNReal.ofReal (s i)) x) := (hfmm.indicator hFm).add (hmF _)
          rw [lintegral_add_left m3, lintegral_add_left m2,
            lintegral_add_left (hfmm.indicator hFm), lintegral_indicator_const hFm,
            lintegral_indicator_const hFm, lintegral_const_mul _ hci]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ F
    · simp only [Set.indicator_of_mem hx, hfp, hfm, hcost, CondPortOT.SingUninf.groundCost, hz]
      have hx1 : x.1 = x0 := (mem_F DX DY x0 xh hA x).1 hx
      rw [hx1]
      set u := ε⁻¹ * L x.2
      set Cc := DX x0 (xh i) + DY x.2 (yh i)
      have hCc : 0 ≤ Cc := add_nonneg (hA.nonneg_X _ _) (hA.nonneg_Y _ _)
      have key := pt_real u (s i) Cc l1 l2 hl1 hCc (hs0 i) (hs i x.2)
      rw [ofReal_max0 u, ofReal_max0 (-l2), ofReal_max0 (-u), ofReal_max0 l2,
        ← ENNReal.ofReal_mul hl1, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
        ← ENNReal.ofReal_add (le_max_right _ _) (hs0 i),
        ← ENNReal.ofReal_add (add_nonneg (le_max_right _ _) (hs0 i)) (mul_nonneg hl1 hCc),
        ← ENNReal.ofReal_add (add_nonneg (add_nonneg (le_max_right _ _) (hs0 i))
          (mul_nonneg hl1 hCc)) (le_max_right _ _)]
      exact ENNReal.ofReal_le_ofReal key
    · simp only [Set.indicator_of_notMem hx, zero_add]
      exact zero_le
  -- summing over `i`
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hW : ∑ i, πi i F = Q F := by
    have := hQint (fun _ => 1) measurable_const
    rw [lintegral_const, one_mul, Measure.restrict_apply_univ] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [lintegral_indicator_const hFm, one_mul]
  have hP : ∑ i, ∫⁻ x, F.indicator fp x ∂(πi i) =
      ENNReal.ofReal ε⁻¹ * ∫⁻ x, ENNReal.ofReal (L x.2) ∂(Q.restrict F) := by
    rw [← hQint fp hfpm, ← lintegral_const_mul (ENNReal.ofReal ε⁻¹) (show Measurable (fun x : X × Y => ENNReal.ofReal (L x.2)) from ENNReal.measurable_ofReal.comp hLm)]
    refine lintegral_congr fun x => ?_
    simp only [hfp]; rw [ENNReal.ofReal_mul (inv_nonneg.2 hε0.le)]
  have hM : ∑ i, ∫⁻ x, F.indicator fm x ∂(πi i) =
      ENNReal.ofReal ε⁻¹ * ∫⁻ x, ENNReal.ofReal (-L x.2) ∂(Q.restrict F) := by
    rw [← hQint fm hfmm, ← lintegral_const_mul (ENNReal.ofReal ε⁻¹) (show Measurable (fun x : X × Y => ENNReal.ofReal (-L x.2)) from ENNReal.measurable_ofReal.comp hLm.neg)]
    refine lintegral_congr fun x => ?_
    simp only [hfm]; rw [← ENNReal.ofReal_mul (inv_nonneg.2 hε0.le)]; ring_nf
  have hS : ∑ i, ENNReal.ofReal (s i) * πi i F ≤ ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, s i) := by
    calc ∑ i, ENNReal.ofReal (s i) * πi i F ≤ ∑ i, ENNReal.ofReal (s i) * (N : ENNReal)⁻¹ :=
          Finset.sum_le_sum fun i _ => by
            gcongr; rw [← hmass i]; exact measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal ((N : ℝ)⁻¹ * ∑ i, s i) := by
          rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun i _ => hs0 i, mul_comm,
            ENNReal.ofReal_mul (inv_nonneg.2 hNpos.le), ENNReal.ofReal_inv_of_pos hNpos,
            ENNReal.ofReal_natCast]
  rw [hW, hP, hM, ← hcost_sum] at hsum
  set Ap := ∫⁻ x, ENNReal.ofReal (L x.2) ∂(Q.restrict F) with hAp
  set Am := ∫⁻ x, ENNReal.ofReal (-L x.2) ∂(Q.restrict F) with hAm
  set m := Q F with hm
  set σ := (N : ℝ)⁻¹ * ∑ i, s i with hσ
  have hσ0 : 0 ≤ σ := mul_nonneg (inv_nonneg.2 hNpos.le) (Finset.sum_nonneg fun i _ => hs0 i)
  have hineq : ENNReal.ofReal ε⁻¹ * Ap + ENNReal.ofReal (-l2) * m ≤
      ENNReal.ofReal ε⁻¹ * Am + ENNReal.ofReal σ + ENNReal.ofReal l1 * ENNReal.ofReal C +
        ENNReal.ofReal l2 * m := by
    refine hsum.trans ?_
    gcongr
  have hmtop : m ≠ ⊤ := measure_ne_top Q F
  have hmpos : 0 < m := lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε0) hQF
  have hmr : ε ≤ m.toReal := (ENNReal.ofReal_le_iff_le_toReal hmtop).1 hQF
  have hmr1 : m.toReal ≤ 1 := by
    have : m ≤ 1 := prob_le_one
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have hmrpos : 0 < m.toReal := lt_of_lt_of_le hε0 hmr
  -- unfold the conditional expectation
  unfold CondPortOT.SingUninf.condExp ModelRiskOT.Duality.extIntegral
  have e1 : (fun p : X × Y => ((L p.2 : ℝ) : EReal).toENNReal) = fun p => ENNReal.ofReal (L p.2) := by
    funext p; rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have e2 : (fun p : X × Y => (-((L p.2 : ℝ) : EReal)).toENNReal) =
      fun p => ENNReal.ofReal (-L p.2) := by
    funext p
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  rw [e1, e2, ← hAp, ← hAm, ← hm]
  by_cases hAmt : Am = ⊤
  · rw [hAmt, EReal.coe_ennreal_top, EReal.sub_top, EReal.coe_mul_bot_of_pos (inv_pos.2 hmrpos)]
    exact bot_le
  have hεinv : ENNReal.ofReal ε⁻¹ ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact inv_pos.2 hε0
  have hrhs : ENNReal.ofReal ε⁻¹ * Am + ENNReal.ofReal σ + ENNReal.ofReal l1 * ENNReal.ofReal C +
        ENNReal.ofReal l2 * m ≠ ⊤ := by
    simp only [ne_eq, ENNReal.add_eq_top, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, hAmt, hmtop,
      false_and, and_false, or_self, not_false_eq_true]
  have hApt : Ap ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hεinv, top_add] at hineq
    exact hrhs (top_le_iff.1 hineq)
  have hr := ENNReal.toReal_mono hrhs hineq
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hApt)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmtop),
    ENNReal.toReal_add (by
      simp only [ne_eq, ENNReal.add_eq_top, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, hAmt,
        false_and, and_false, or_self, not_false_eq_true])
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmtop),
    ENNReal.toReal_add (by
      simp only [ne_eq, ENNReal.add_eq_top, ENNReal.mul_eq_top, ENNReal.ofReal_ne_top, hAmt,
        false_and, and_false, or_self, not_false_eq_true])
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAmt) ENNReal.ofReal_ne_top] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', max_eq_left (inv_nonneg.2 hε0.le),
    max_eq_left hσ0, max_eq_left hl1, max_eq_left hC0] at hr
  have hc : ((Ap : EReal) - (Am : EReal)) = (((Ap.toReal - Am.toReal : ℝ)) : EReal) := by
    rw [EReal.coe_sub, EReal.coe_ennreal_toReal hApt, EReal.coe_ennreal_toReal hAmt]
  rw [hc, ← EReal.coe_mul, EReal.coe_le_coe_iff]
  set ap := Ap.toReal
  set am := Am.toReal
  set mr := m.toReal
  have hl2 : max l2 0 - max (-l2) 0 = l2 := by
    rcases le_total 0 l2 with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  -- `ε⁻¹ (ap - am) ≤ σ + l1 C + l2 mr`
  have h1 : ap - am ≤ ε * (σ + l1 * C) + ε * l2 * mr := by
    have h2 : ε⁻¹ * (ap - am) ≤ σ + l1 * C + l2 * mr := by
      have : (max l2 0 - max (-l2) 0) * mr = l2 * mr := by rw [hl2]
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hε0.le
    rw [← mul_assoc, mul_inv_cancel₀ hε0.ne', one_mul] at h3
    linarith
  have hσC : 0 ≤ σ + l1 * C := add_nonneg hσ0 (mul_nonneg hl1 hC0)
  have h4 : mr⁻¹ * (ap - am) ≤ mr⁻¹ * (ε * (σ + l1 * C)) + ε * l2 := by
    have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hmrpos.le)
    rw [mul_add, show mr⁻¹ * (ε * l2 * mr) = ε * l2 by field_simp] at this
    exact this
  have h5 : mr⁻¹ * (ε * (σ + l1 * C)) ≤ σ + l1 * C := by
    rw [← mul_assoc]
    have : mr⁻¹ * ε ≤ 1 := by rw [inv_mul_le_iff₀ hmrpos]; linarith
    nlinarith
  linarith


/-- A strictly feasible weight vector from `ρ > ρ_min`. -/
theorem slater (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X)
    (yh : Fin N → Y) (x0 : X) (hA : CondPortOT.SingDual.Assumption24 DX DY x0 0 xh)
    (ε : ℝ) (hε0 : 0 < ε) (ρ : ℝ)
    (hρ : CondPortOT.SingDual.rhoMin DX DY xh yh x0 0 ε < ENNReal.ofReal ρ) :
    ∃ υ : Fin N → ℝ, (∀ i, 0 ≤ υ i ∧ υ i ≤ 1) ∧ ∑ i, υ i = N * ε ∧
      (N : ℝ)⁻¹ * ∑ i, υ i * DX x0 (xh i) < ρ := by
  classical
  set F := CondPortOT.SingUninf.fiber (Y := Y) DX x0 0 with hF
  have hFm : MeasurableSet F := F_meas DX DY x0 xh hA
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨Q, ⟨hQp, hQF⟩, hQc⟩ : ∃ Q : Measure (X × Y),
      (IsProbabilityMeasure Q ∧ ENNReal.ofReal ε ≤ Q F) ∧
      RWPI.SqrtLasso.transportCost (CondPortOT.SingUninf.groundCost DX DY) Q
        (CondPortOT.SingUninf.empirical xh yh) < ENNReal.ofReal ρ := by
    have := hρ
    unfold CondPortOT.SingDual.rhoMin at this
    simp only [iInf_lt_iff] at this
    obtain ⟨Q, h1, h2⟩ := this
    exact ⟨Q, h1, h2⟩
  obtain ⟨π, ⟨hπp, hπ1, hπ2⟩, hπc⟩ : ∃ π : Measure ((X × Y) × (X × Y)),
      (IsProbabilityMeasure π ∧ π.map Prod.fst = Q ∧
        π.map Prod.snd = CondPortOT.SingUninf.empirical xh yh) ∧
      ∫⁻ w, CondPortOT.SingUninf.groundCost DX DY w.1 w.2 ∂π < ENNReal.ofReal ρ := by
    have := hQc
    unfold RWPI.SqrtLasso.transportCost at this
    simp only [iInf_lt_iff] at this
    obtain ⟨π, h1, h2⟩ := this
    exact ⟨π, h1, h2⟩
  set z : Fin N → X × Y := fun i => (xh i, yh i) with hz
  obtain ⟨πi, hmass, hint⟩ := decomp z π (by rw [hπ2]; rfl)
  have hcm := gc_meas DX DY hA.cont_X hA.cont_Y
  have hNinv : (N : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by exact_mod_cast hN.ne')
  have hπfin : ∀ i, πi i F ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (by rw [hmass i]; exact hNinv) (measure_mono (Set.subset_univ _))
  have hle : ∀ i, (πi i F).toReal ≤ (N : ℝ)⁻¹ := by
    intro i
    have := ENNReal.toReal_mono (by rw [hmass i]; exact hNinv) (measure_mono (μ := πi i)
      (Set.subset_univ F))
    rwa [hmass i, ENNReal.toReal_inv, ENNReal.toReal_natCast] at this
  have hQF' : Q F = ∑ i, πi i F := by
    rw [← hπ1, Measure.map_apply measurable_fst hFm]
    have h := hint (fun w => F.indicator 1 w.1) ((measurable_one.indicator hFm).comp measurable_fst)
    have e : (fun w : (X × Y) × (X × Y) => F.indicator (1 : X × Y → ENNReal) w.1) =
        (Prod.fst ⁻¹' F).indicator 1 := by
      ext w; simp [Set.indicator_apply]
    rw [e, lintegral_indicator_one (hFm.preimage measurable_fst)] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => lintegral_indicator_one hFm
  set q : Fin N → ℝ := fun i => (πi i F).toReal with hq
  have hq0 : ∀ i, 0 ≤ q i := fun i => ENNReal.toReal_nonneg
  have hQtop : Q F ≠ ⊤ := measure_ne_top Q F
  have hsumq : ε ≤ ∑ i, q i := by
    have : (Q F).toReal = ∑ i, q i := by rw [hQF', ENNReal.toReal_sum fun i _ => hπfin i]
    rw [← this]; exact (ENNReal.ofReal_le_iff_le_toReal hQtop).1 hQF
  -- cost lower bound
  have hcostlow : ∑ i, q i * DX x0 (xh i) < ρ := by
    have hpt : ∀ i, ENNReal.ofReal (DX x0 (xh i)) * πi i F ≤
        ∫⁻ x, CondPortOT.SingUninf.groundCost DX DY x (z i) ∂(πi i) := by
      intro i
      rw [← lintegral_indicator_const hFm]
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ F
      · rw [Set.indicator_of_mem hx]
        unfold CondPortOT.SingUninf.groundCost
        apply ENNReal.ofReal_le_ofReal
        rw [(mem_F DX DY x0 xh hA x).1 hx]
        linarith [hA.nonneg_Y x.2 (yh i)]
      · rw [Set.indicator_of_notMem hx]; exact zero_le
    have h1 : ∑ i, ENNReal.ofReal (DX x0 (xh i)) * πi i F < ENNReal.ofReal ρ :=
      lt_of_le_of_lt ((Finset.sum_le_sum fun i _ => hpt i).trans
        (le_of_eq (hint _ hcm).symm)) hπc
    have h2 : ∑ i, ENNReal.ofReal (DX x0 (xh i)) * πi i F =
        ENNReal.ofReal (∑ i, q i * DX x0 (xh i)) := by
      rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hq0 i) (hA.nonneg_X _ _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, ENNReal.ofReal_mul (hq0 i), hq, ENNReal.ofReal_toReal (hπfin i)]
    rw [h2] at h1
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (Finset.sum_nonneg fun i _ => mul_nonneg (hq0 i) (hA.nonneg_X _ _))).1 h1
  set S := ∑ i, q i with hS
  have hSpos : 0 < S := lt_of_lt_of_le hε0 hsumq
  set k := ε / S with hk
  have hk0 : 0 ≤ k := div_nonneg hε0.le hSpos.le
  have hk1 : k ≤ 1 := by rw [hk, div_le_one hSpos]; exact hsumq
  refine ⟨fun i => N * q i * k, fun i => ⟨by positivity, ?_⟩, ?_, ?_⟩
  · have h1 : (N : ℝ) * q i ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (hle i) hNpos.le
      rwa [mul_inv_cancel₀ hNpos.ne'] at this
    calc (N : ℝ) * q i * k ≤ 1 * 1 := mul_le_mul h1 hk1 hk0 zero_le_one
      _ = 1 := one_mul 1
  · rw [← Finset.sum_mul, ← Finset.mul_sum, ← hS, hk]; field_simp
  · have : (N : ℝ)⁻¹ * ∑ i, N * q i * k * DX x0 (xh i) = k * ∑ i, q i * DX x0 (xh i) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [this]
    have hc0 : 0 ≤ ∑ i, q i * DX x0 (xh i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hq0 i) (hA.nonneg_X _ _)
    nlinarith

end W

end SDMainAux

-- ===== SD_E.lean

namespace SDMainAux

lemma ereal_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (((∑ i ∈ s, f i : ℝ)) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma ereal_coe_max (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.2 h)]
  · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.2 h)]

lemma ereal_sum_top {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → EReal)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (i : ι) (hi : i ∈ s) (htop : f i = ⊤) : ∑ j ∈ s, f j = ⊤ := by
  rw [← Finset.add_sum_erase s f hi, htop]
  apply EReal.top_add_of_ne_bot
  have : 0 ≤ ∑ j ∈ s.erase i, f j :=
    Finset.sum_nonneg fun j hj => h0 j (Finset.mem_of_mem_erase hj)
  intro hb; rw [hb] at this; exact absurd this (by simp)

lemma ereal_iSup_coe {ι : Type*} [Nonempty ι] (f : ι → ℝ) (hf : BddAbove (Set.range f)) :
    ⨆ i, ((f i : ℝ) : EReal) = (((⨆ i, f i : ℝ)) : EReal) := by
  apply le_antisymm
  · exact iSup_le fun i => EReal.coe_le_coe_iff.2 (le_ciSup hf i)
  · rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    apply EReal.coe_le_coe_iff.2
    apply ciSup_le
    intro i
    have := (le_iSup (fun i => ((f i : ℝ) : EReal)) i).trans hz.le
    exact EReal.coe_le_coe_iff.1 this

lemma ereal_le_of_forall {x : EReal} {b k : ℝ} (hk : 0 ≤ k)
    (h : ∀ δ : ℝ, 0 < δ → x ≤ ((b + δ * k : ℝ) : EReal)) : x ≤ (b : EReal) := by
  induction x using EReal.rec with
  | bot => exact bot_le
  | top =>
    have := h 1 one_pos
    rw [top_le_iff] at this
    exact absurd this (EReal.coe_ne_top _)
  | coe r =>
    apply EReal.coe_le_coe_iff.2
    apply le_of_forall_pos_le_add
    intro e he
    have := EReal.coe_le_coe_iff.1 (h (e / (k + 1)) (div_pos he (by linarith)))
    have h2 : e / (k + 1) * k ≤ e := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
    linarith

lemma single_sum_apply_nonneg {N : ℕ} {Y : Type*} (υ : Fin N → ℝ) (hυ : ∀ i, 0 ≤ υ i)
    (y : Fin N → Y) (p : Fin N × Y) :
    0 ≤ (∑ i, υ i • Finsupp.single (i, y i) (1 : ℝ)) p := by
  rw [Finsupp.finset_sum_apply]
  exact Finset.sum_nonneg fun i _ => by
    rw [Finsupp.smul_apply, smul_eq_mul]
    classical
    exact mul_nonneg (hυ i) (by rw [Finsupp.single_apply]; split_ifs <;> norm_num)

lemma Lam_single_sum {N : ℕ} {Y : Type*} (w : Fin N × Y → ℝ) (υ : Fin N → ℝ) (y : Fin N → Y) :
    Lam w (∑ i, υ i • Finsupp.single (i, y i) (1 : ℝ)) = ∑ i, υ i * w (i, y i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Lam, Finsupp.linearCombination_single, one_smul, smul_eq_mul]

end SDMainAux

open SDMainAux in
theorem solution {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (DX : X → X → ℝ) (DY : Y → Y → ℝ) {N : ℕ} (hN : 0 < N) (xh : Fin N → X) (yh : Fin N → Y)
    (x0 : X) (hA : CondPortOT.SingDual.Assumption24 DX DY x0 0 xh) (hH1 : CondPortOT.SingUninf.NotIsolated DX x0)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ρ : ℝ) (hρ : CondPortOT.SingDual.rhoMin DX DY xh yh x0 0 ε < ENNReal.ofReal ρ)
    (L : Y → ℝ) (hL : Measurable L) :
    CondPortOT.SingDual.worstCaseGe DX DY xh yh x0 0 ρ ε L =
      ⨅ (l1 : ℝ) (_ : 0 ≤ l1) (l2 : ℝ),
        ((ρ * l1 + ε * l2 : ℝ) : EReal) + (((N : ℝ)⁻¹ : ℝ) : EReal) *
          ∑ i, max (⨆ y, ((ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 - l2 : ℝ) : EReal)) 0 := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ0 : 0 < ρ := by
    have : (0 : ENNReal) < ENNReal.ofReal ρ := lt_of_le_of_lt (by simp) hρ
    exact ENNReal.ofReal_pos.1 this
  haveI : Nonempty Y := ⟨yh ⟨0, hN⟩⟩
  apply le_antisymm
  · -- weak duality
    refine le_iInf fun l1 => le_iInf fun hl1 => le_iInf fun l2 => ?_
    unfold CondPortOT.SingDual.worstCaseGe
    refine iSup₂_le fun Q hQ => ?_
    obtain ⟨⟨hQp, hQc⟩, hQF⟩ := hQ
    set H : Fin N → EReal := fun i =>
      ⨆ y, ((ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 - l2 : ℝ) : EReal) with hH
    show _ ≤ ((ρ * l1 + ε * l2 : ℝ) : EReal) + (((N : ℝ)⁻¹ : ℝ) : EReal) * ∑ j, max (H j) 0
    by_cases htop : ∃ i, H i = ⊤
    · obtain ⟨i, hi⟩ := htop
      have hsum : ∑ j, max (H j) 0 = ⊤ :=
        ereal_sum_top _ _ (fun j _ => le_max_right _ _) i (Finset.mem_univ _)
          (by rw [hi]; exact max_eq_left le_top)
      rw [hsum, EReal.coe_mul_top_of_pos (inv_pos.2 hNpos), EReal.coe_add_top]
      exact le_top
    push_neg at htop
    set s : Fin N → ℝ := fun i => (max (H i) 0).toReal with hs
    have hsH : ∀ i, max (H i) 0 = ((s i : ℝ) : EReal) := by
      intro i
      rw [hs, EReal.coe_toReal]
      · exact ne_of_lt (max_lt (lt_top_iff_ne_top.2 (htop i)) EReal.zero_lt_top)
      · exact ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (le_max_right _ _))
    have hs0 : ∀ i, 0 ≤ s i := fun i => EReal.toReal_nonneg (le_max_right _ _)
    have hsb : ∀ i y, ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 - l2 ≤ s i := by
      intro i y
      have h1 : ((ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 - l2 : ℝ) : EReal) ≤
          ((s i : ℝ) : EReal) := by
        rw [← hsH]
        exact (le_iSup (fun y => ((ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 - l2 : ℝ) :
          EReal)) y).trans (le_max_left _ _)
      exact EReal.coe_le_coe_iff.1 h1
    have hT : ((ρ * l1 + ε * l2 : ℝ) : EReal) + (((N : ℝ)⁻¹ : ℝ) : EReal) * ∑ j, max (H j) 0 =
        ((ρ * l1 + ε * l2 + (N : ℝ)⁻¹ * ∑ j, s j : ℝ) : EReal) := by
      simp only [hsH]
      rw [← ereal_coe_sum, ← EReal.coe_mul, ← EReal.coe_add]
    rw [hT]
    haveI := hQp
    refine ereal_le_of_forall hl1 fun δ hδ => ?_
    obtain ⟨π, ⟨_, hπ1, hπ2⟩, hπc⟩ : ∃ π : Measure ((X × Y) × (X × Y)),
        (IsProbabilityMeasure π ∧ π.map Prod.fst = Q ∧
          π.map Prod.snd = CondPortOT.SingUninf.empirical xh yh) ∧
        ∫⁻ w, CondPortOT.SingUninf.groundCost DX DY w.1 w.2 ∂π < ENNReal.ofReal (ρ + δ) := by
      have h1 : RWPI.SqrtLasso.transportCost (CondPortOT.SingUninf.groundCost DX DY) Q
          (CondPortOT.SingUninf.empirical xh yh) < ENNReal.ofReal (ρ + δ) :=
        lt_of_le_of_lt hQc ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
      unfold RWPI.SqrtLasso.transportCost at h1
      simp only [iInf_lt_iff] at h1
      obtain ⟨π, h1, h2⟩ := h1
      exact ⟨π, h1, h2⟩
    have := weak_core DX DY hN xh yh x0 hA ε hε0 hε1 L hL l1 l2 hl1 s hs0 hsb Q hQF π hπ1 hπ2
      (ρ + δ) (by linarith) hπc.le
    refine this.trans (le_of_eq ?_)
    congr 1; ring
  · -- strong duality
    rw [← EReal.le_of_forall_lt_iff_le]
    intro t ht
    set mass : Fin N → ((Fin N × Y) →₀ ℝ) →ₗ[ℝ] ℝ :=
      fun i => Lam (fun p : Fin N × Y => if p.1 = i then (1 : ℝ) else 0) with hmass
    set Cs : Set ((Fin N × Y) →₀ ℝ) :=
      {ν | (∀ p, 0 ≤ ν p) ∧ (∀ i, mass i ν ≤ 1) ∧ ∑ i, mass i ν = N * ε} with hCs_def
    set Aop : ((Fin N × Y) →₀ ℝ) →ₗ[ℝ] ℝ :=
      (N : ℝ)⁻¹ • Lam (fun p : Fin N × Y => DX x0 (xh p.1) + DY p.2 (yh p.1)) with hAop
    set Vop : ((Fin N × Y) →₀ ℝ) →ₗ[ℝ] ℝ :=
      ((N : ℝ) * ε)⁻¹ • Lam (fun p : Fin N × Y => L p.2) with hVop
    have hCs : Convex ℝ Cs := by
      intro ν hν ν' hν' a b ha hb hab
      refine ⟨fun p => ?_, fun i => ?_, ?_⟩
      · simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg ha (hν.1 p)) (mul_nonneg hb (hν'.1 p))
      · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        nlinarith [hν.2.1 i, hν'.2.1 i]
      · simp only [map_add, map_smul, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
          hν.2.2, hν'.2.2]
        rw [← add_mul, hab, one_mul]
    have hmemC : ∀ (υ : Fin N → ℝ) (y : Fin N → Y), (∀ i, 0 ≤ υ i ∧ υ i ≤ 1) →
        ∑ i, υ i = N * ε → (∑ i, υ i • Finsupp.single (i, y i) (1 : ℝ)) ∈ Cs := by
      intro υ y h1 h2
      have hm : ∀ j, mass j (∑ i, υ i • Finsupp.single (i, y i) (1 : ℝ)) = υ j := by
        intro j
        simp only [hmass]
        rw [Lam_single_sum]
        simp
      refine ⟨single_sum_apply_nonneg υ (fun i => (h1 i).1) y, fun j => by rw [hm]; exact (h1 j).2,
        by simp only [hm]; exact h2⟩
    obtain ⟨υ0, hυ0, hυ0s, hυ0c⟩ := slater DX DY hN xh yh x0 hA ε hε0 ρ hρ
    have hA0 : Aop (∑ i, υ0 i • Finsupp.single (i, yh i) (1 : ℝ)) < ρ := by
      simp only [hAop, LinearMap.smul_apply, smul_eq_mul]
      rw [Lam_single_sum]
      simp only [DY_self DX DY x0 xh hA, add_zero]
      exact hυ0c
    have hfeas : ∀ ν ∈ Cs, Aop ν < ρ → Vop ν ≤ t := by
      intro ν hν hAν
      simp only [hAop, LinearMap.smul_apply, smul_eq_mul] at hAν
      obtain ⟨Q, hQB, hQF, hQce⟩ :=
        qcon DX DY hN xh yh x0 hA hH1 ε hε0 hε1 ρ L ν hν.1 hν.2.1 hν.2.2 hAν
      have h1 : ((Vop ν : ℝ) : EReal) ≤ CondPortOT.SingDual.worstCaseGe DX DY xh yh x0 0 ρ ε L := by
        unfold CondPortOT.SingDual.worstCaseGe
        refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun Q (_ : CondPortOT.SingUninf.InBall DX DY xh yh ρ Q ∧
          ENNReal.ofReal ε ≤ Q (CondPortOT.SingUninf.fiber DX x0 0)) =>
            CondPortOT.SingUninf.condExp Q (CondPortOT.SingUninf.fiber DX x0 0) L) Q ⟨hQB, hQF⟩)
        rw [hQce]
        simp only [hVop, LinearMap.smul_apply, smul_eq_mul]
      exact EReal.coe_le_coe_iff.1 (h1.trans ht.le)
    obtain ⟨l1, hl1, hsep⟩ := sep2 Cs hCs Aop Vop ρ t _ (hmemC υ0 yh hυ0 hυ0s) hA0 hfeas
    set g : Fin N → Y → ℝ := fun i y => ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 with hg
    have hkey : ∀ (υ : Fin N → ℝ) (y : Fin N → Y), (∀ i, 0 ≤ υ i ∧ υ i ≤ 1) → ∑ i, υ i = N * ε →
        ∑ i, υ i * g i (y i) ≤ N * (t - ρ * l1) := by
      intro υ y h1 h2
      have := hsep _ (hmemC υ y h1 h2)
      simp only [hAop, hVop, LinearMap.smul_apply, smul_eq_mul, Lam_single_sum] at this
      set SL := ∑ i, υ i * L (y i) with hSL
      set SC := ∑ i, υ i * (DX x0 (xh i) + DY (y i) (yh i)) with hSC
      have e1 : ∑ i, υ i * g i (y i) = ε⁻¹ * SL - l1 * SC := by
        rw [hSL, hSC, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have e2 : ε⁻¹ * SL - l1 * SC =
          N * (((N : ℝ) * ε)⁻¹ * SL + l1 * (ρ - (N : ℝ)⁻¹ * SC)) - N * ρ * l1 := by
        field_simp
        ring
      rw [e1, e2]
      nlinarith [mul_le_mul_of_nonneg_left this hNpos.le]
    have hbdd : ∀ i, BddAbove (Set.range (g i)) := by
      intro i
      refine ⟨(N * (t - ρ * l1) - ε * ∑ j ∈ Finset.univ.erase i, g j (yh j)) / ε, ?_⟩
      rintro _ ⟨y, rfl⟩
      have := hkey (fun _ => ε) (Function.update yh i y) (fun _ => ⟨hε0.le, hε1⟩) (by simp)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
      simp only [Function.update_self] at this
      have e2 : ∑ j ∈ Finset.univ.erase i, ε * g j (Function.update yh i y j) =
          ε * ∑ j ∈ Finset.univ.erase i, g j (yh j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [e2] at this
      rw [le_div_iff₀ hε0]
      linarith
    set G : Fin N → ℝ := fun i => ⨆ y, g i y with hG
    have hGb : ∀ υ : Fin N → ℝ, (∀ i, 0 ≤ υ i ∧ υ i ≤ 1) → ∑ i, υ i = N * ε →
        ∑ i, υ i * G i ≤ N * (t - ρ * l1) := by
      intro υ h1 h2
      apply le_of_forall_pos_le_add
      intro η hη
      have hη' : 0 < η / (N * ε) := by positivity
      have hy : ∀ i, ∃ y, G i - η / (N * ε) < g i y := fun i =>
        exists_lt_of_lt_ciSup (by simp only [hG]; linarith)
      choose y hy using hy
      have h3 := hkey υ y h1 h2
      have h4 : ∑ i, υ i * G i ≤ ∑ i, (υ i * g i (y i) + υ i * (η / (N * ε))) :=
        Finset.sum_le_sum fun i _ => by nlinarith [hy i, (h1 i).1]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, h2] at h4
      have h5 : (N : ℝ) * ε * (η / (N * ε)) = η := by field_simp
      linarith
    obtain ⟨l2, υs, hυs, hυss, hcv⟩ := cvar hN ε hε0 hε1 G
    have hHi : ∀ i, ⨆ y, ((ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 - l2 : ℝ) : EReal) =
        ((G i - l2 : ℝ) : EReal) := by
      intro i
      have hb2 : BddAbove (Set.range fun y => ε⁻¹ * L y - (DX x0 (xh i) + DY y (yh i)) * l1 - l2) := by
        obtain ⟨b, hb⟩ := hbdd i
        refine ⟨b - l2, ?_⟩
        rintro _ ⟨y, rfl⟩
        have := hb ⟨y, rfl⟩
        simp only [hg] at this
        linarith
      rw [ereal_iSup_coe _ hb2]
      congr 1
      rw [show G i = ⨆ y, g i y from rfl, ciSup_sub (hbdd i)]
    refine (iInf_le_of_le l1 (iInf_le_of_le hl1 (iInf_le_of_le l2 le_rfl))).trans ?_
    simp only [hHi]
    have hmx : ∀ i, max ((G i - l2 : ℝ) : EReal) 0 = ((max (G i - l2) 0 : ℝ) : EReal) := by
      intro i; rw [ereal_coe_max, EReal.coe_zero]
    simp only [hmx]
    rw [← ereal_coe_sum, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have h := hGb υs hυs hυss
    rw [← hcv] at h
    have h6 : (N : ℝ)⁻¹ * ∑ i, max (G i - l2) 0 ≤ t - ρ * l1 - ε * l2 := by
      rw [inv_mul_le_iff₀ hNpos]; nlinarith
    linarith


