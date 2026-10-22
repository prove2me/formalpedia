-- Prove2me | solution 1 for DiscreteConvex.IntegralConvexityC.prop_3_30_argmin_nonempty_integer_valued
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:11:06.957914+00:00
-- url     : https://prove2.me/submissions/13d76ba8-5405-4760-9118-01201107e5e6

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexityC_InfPerturbed
import Definitions.Def_DiscreteConvex_IntegralConvexityC_CastZR



namespace DiscreteConvex.IntegralConvexityC

lemma p330_sum_lin {n : ℕ} (p : Fin n → ℝ) (x y : Fin n → ℤ) (ε : ℝ) :
    ∑ i, p i * ((x i : ℝ) + ε * ((y i : ℝ) - x i)) =
      ∑ i, p i * (x i : ℝ) + ε * (∑ i, p i * (y i : ℝ) - ∑ i, p i * (x i : ℝ)) := by
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_); ring

lemma p330_sum_sub {n : ℕ} (p : Fin n → ℝ) (x w : Fin n → ℤ) :
    ∑ i, p i * (((w - x) i : ℤ) : ℝ) = ∑ i, p i * (w i : ℝ) - ∑ i, p i * (x i : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.sub_apply, Int.cast_sub]; ring

/-- local optimality (over the cube of radius one) implies global optimality of the perturbed
function, for an integrally convex `f`. -/
lemma p330_local_global {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (hic : IntegrallyConvex f)
    (p : Fin n → ℝ) (x : Fin n → ℤ) (fx : ℝ) (hfx : f x = (fx : WithTop ℝ))
    (hloc : ∀ w : Fin n → ℤ, (∀ i, x i - 1 ≤ w i ∧ w i ≤ x i + 1) →
      ((fx - ∑ i, p i * (x i : ℝ) + ∑ i, p i * (w i : ℝ) : ℝ) : WithTop ℝ) ≤ f w) :
    x ∈ ArgMinPerturbed f p := by
  intro y
  by_contra hlt
  push_neg at hlt
  have hy' : f y ≠ ⊤ := by
    intro h; rw [h, top_add] at hlt; exact not_top_lt hlt
  obtain ⟨fy, hfy⟩ := WithTop.ne_top_iff_exists.mp hy'
  rw [← hfy, hfx] at hlt
  have hlt' : fy + ∑ i, p i * (x i : ℝ) < fx + ∑ i, p i * (y i : ℝ) := by
    rw [← WithTop.coe_add, ← WithTop.coe_add] at hlt
    exact WithTop.coe_lt_coe.mp hlt
  set D : ℝ := ∑ i, |(y i : ℝ) - x i| with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hdiD : ∀ i, |(y i : ℝ) - x i| ≤ D := fun i =>
    Finset.single_le_sum (f := fun i => |(y i : ℝ) - x i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
  set ε : ℝ := 1 / (D + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one (by linarith)]; linarith
  have hεd : ∀ i, |ε * ((y i : ℝ) - x i)| ≤ 1 := by
    intro i
    rw [abs_mul, abs_of_pos hε0]
    have hD1 : 0 < D + 1 := by linarith
    rw [hε, div_mul_eq_mul_div, one_mul, div_le_one hD1]
    linarith [hdiD i]
  set z : Fin n → ℝ := fun i => (x i : ℝ) + ε * ((y i : ℝ) - x i) with hz
  have hnb : ∀ w ∈ IntegralNeighborhood z, ∀ i, x i - 1 ≤ w i ∧ w i ≤ x i + 1 := by
    intro w hw i
    have h1 := (hw i).1
    have h2 := (hw i).2
    have ha := abs_le.mp (hεd i)
    have h3 : x i - 1 ≤ ⌊z i⌋ := Int.le_floor.mpr (by
      simp only [hz]; push_cast; linarith [ha.1])
    have h4 : ⌈z i⌉ ≤ x i + 1 := Int.ceil_le.mpr (by
      simp only [hz]; push_cast; linarith [ha.2])
    constructor <;> omega
  -- lower bound on the local convex extension
  have hL : ((fx - ∑ i, p i * (x i : ℝ) + ∑ i, p i * z i : ℝ) : EReal) ≤
      LocalConvexExtension f z := by
    unfold LocalConvexExtension
    refine le_sSup ⟨p, fx - ∑ i, p i * (x i : ℝ), fun w hw => ?_, rfl⟩
    exact WithBot.coe_le_coe.mpr (hloc w (hnb w hw))
  -- upper bound on the convex closure
  have hU : ConvexClosure f z ≤ (((1 - ε) * fx + ε * fy : ℝ) : EReal) := by
    unfold ConvexClosure
    refine sSup_le (fun v hv => ?_)
    obtain ⟨q, a, hmin, rfl⟩ := hv
    have h1 := hmin x
    have h2 := hmin y
    rw [hfx] at h1
    rw [← hfy] at h2
    have h1' : a + ∑ i, q i * (x i : ℝ) ≤ fx := EReal.coe_le_coe_iff.mp h1
    have h2' : a + ∑ i, q i * (y i : ℝ) ≤ fy := EReal.coe_le_coe_iff.mp h2
    have hs : ∑ i, q i * z i = ∑ i, q i * (x i : ℝ) +
        ε * (∑ i, q i * (y i : ℝ) - ∑ i, q i * (x i : ℝ)) := p330_sum_lin q x y ε
    rw [EReal.coe_le_coe_iff, hs]
    nlinarith [mul_le_mul_of_nonneg_left h1' (sub_nonneg.mpr hε1),
      mul_le_mul_of_nonneg_left h2' hε0.le]
  rw [hic z] at hL
  have hfin := EReal.coe_le_coe_iff.mp (le_trans hL hU)
  have hs : ∑ i, p i * z i = ∑ i, p i * (x i : ℝ) +
      ε * (∑ i, p i * (y i : ℝ) - ∑ i, p i * (x i : ℝ)) := p330_sum_lin p x y ε
  rw [hs] at hfin
  have := mul_pos hε0 (sub_pos.mpr hlt')
  nlinarith

lemma p330_cast {n : ℕ} (f : (Fin n → ℤ) → WithTop ℤ) (x : Fin n → ℤ) :
    CastZR f x = ⊤ ∨ ∃ k : ℤ, f x = (k : WithTop ℤ) ∧ CastZR f x = ((k : ℝ) : WithTop ℝ) := by
  unfold CastZR
  cases h : f x with
  | top => left; rfl
  | coe k => right; exact ⟨k, rfl, rfl⟩

theorem p330_core {n : ℕ} (f : (Fin n → ℤ) → WithTop ℤ)
    (hic : IntegrallyConvex (CastZR f)) (p : Fin n → ℝ)
    (hinf : InfPerturbed (CastZR f) p > ⊥) :
    (ArgMinPerturbed (CastZR f) p).Nonempty := by
  classical
  set g := CastZR f with hg
  have hc : ∀ x : Fin n → ℤ, g x = ⊤ ∨ ∃ k : ℤ, f x = (k : WithTop ℤ) ∧ g x = ((k : ℝ) : WithTop ℝ) :=
    fun x => p330_cast f x
  by_cases hall : ∀ y, g y = ⊤
  · refine ⟨0, fun y => ?_⟩
    rw [hall y, top_add]; exact le_top
  push_neg at hall
  obtain ⟨x0, hx0⟩ := hall
  -- the infimum is a real number
  set S : Set EReal := {v : EReal | ∃ x : Fin n → ℤ,
    v = ToEReal3 (g x) - ((∑ i, p i * (x i : ℝ) : ℝ) : EReal)} with hS
  have hinf' : sInf S > ⊥ := hinf
  have hmem : ∀ x : Fin n → ℤ, ToEReal3 (g x) - ((∑ i, p i * (x i : ℝ) : ℝ) : EReal) ∈ S :=
    fun x => ⟨x, rfl⟩
  have hlow : ∀ x : Fin n → ℤ, sInf S ≤ ToEReal3 (g x) - ((∑ i, p i * (x i : ℝ) : ℝ) : EReal) :=
    fun x => sInf_le (hmem x)
  have hcast : ∀ x : Fin n → ℤ, ∀ k : ℤ, g x = ((k : ℝ) : WithTop ℝ) →
      ToEReal3 (g x) - ((∑ i, p i * (x i : ℝ) : ℝ) : EReal) =
        (((k : ℝ) - ∑ i, p i * (x i : ℝ) : ℝ) : EReal) := by
    intro x k hk
    rw [EReal.coe_sub]
    unfold ToEReal3
    rw [hk]; rfl
  have hne_top : sInf S ≠ ⊤ := by
    rcases hc x0 with h | ⟨k, _, hk⟩
    · exact absurd h hx0
    · intro htop
      have := hlow x0
      rw [htop, hcast x0 k hk] at this
      exact absurd this (not_le.mpr (EReal.coe_lt_top _))
  set mr : ℝ := (sInf S).toReal with hmr
  have hmr_eq : ((mr : ℝ) : EReal) = sInf S := EReal.coe_toReal hne_top (ne_of_gt hinf')
  -- the gap δ
  set Dset : Finset (Fin n → ℤ) := Finset.Icc (fun _ => -1) (fun _ => 1) with hDset
  have hDne : Dset.Nonempty := ⟨0, by
    rw [hDset, Finset.mem_Icc]; constructor <;> intro i <;> simp⟩
  set gap : (Fin n → ℤ) → ℝ := fun d =>
    (∑ i, p i * (d i : ℝ)) + 1 - ⌈∑ i, p i * (d i : ℝ)⌉ with hgap
  set δ : ℝ := Dset.inf' hDne gap with hδ
  have hδ0 : 0 < δ := by
    rw [hδ, Finset.lt_inf'_iff]
    intro d _
    simp only [hgap]
    linarith [Int.ceil_lt_add_one (∑ i, p i * (d i : ℝ))]
  have hδle : ∀ d ∈ Dset, δ ≤ gap d := fun d hd => Finset.inf'_le gap hd
  -- a point within δ of the infimum
  have hlt : sInf S < ((mr + δ : ℝ) : EReal) := by
    rw [← hmr_eq]; exact_mod_cast (by linarith : mr < mr + δ)
  obtain ⟨v, ⟨x, rfl⟩, hvlt⟩ := sInf_lt_iff.mp hlt
  obtain ⟨kx, hfx, hgx⟩ : ∃ k : ℤ, f x = (k : WithTop ℤ) ∧ g x = ((k : ℝ) : WithTop ℝ) := by
    rcases hc x with h | h
    · exfalso
      have : ToEReal3 (g x) = ⊤ := by unfold ToEReal3; rw [h]; rfl
      rw [this, EReal.top_sub_coe] at hvlt
      exact not_top_lt hvlt
    · exact h
  rw [hcast x kx hgx] at hvlt
  have hvlt' : (kx : ℝ) - ∑ i, p i * (x i : ℝ) < mr + δ := EReal.coe_lt_coe_iff.mp hvlt
  refine ⟨x, p330_local_global g hic p x kx hgx ?_⟩
  intro w hw
  rcases hc w with h | ⟨kw, _, hkw⟩
  · rw [h]; exact le_top
  rw [hkw]
  apply WithTop.coe_le_coe.mpr
  have hlw := hlow w
  rw [hcast w kw hkw, ← hmr_eq] at hlw
  have hlw' : mr ≤ (kw : ℝ) - ∑ i, p i * (w i : ℝ) := EReal.coe_le_coe_iff.mp hlw
  have hd : w - x ∈ Dset := by
    rw [hDset, Finset.mem_Icc]
    constructor <;> intro i <;> simp only [Pi.sub_apply] <;> linarith [(hw i).1, (hw i).2]
  have hgd := hδle _ hd
  simp only [hgap, p330_sum_sub] at hgd
  set s : ℝ := ∑ i, p i * (w i : ℝ) - ∑ i, p i * (x i : ℝ) with hs
  have h1 : ((⌈s⌉ : ℤ) : ℝ) - 1 < ((kw - kx : ℤ) : ℝ) := by push_cast; linarith
  have h2 : ⌈s⌉ - 1 < kw - kx := by exact_mod_cast h1
  have h3 : ⌈s⌉ ≤ kw - kx := by omega
  have h4 : (⌈s⌉ : ℝ) ≤ ((kw - kx : ℤ) : ℝ) := by exact_mod_cast h3
  have h5 := Int.le_ceil s
  push_cast at h4
  linarith

end DiscreteConvex.IntegralConvexityC

open DiscreteConvex.IntegralConvexityC


theorem solution {n : ℕ} (f : (Fin n → ℤ) → WithTop ℤ)
    (hic : IntegrallyConvex (CastZR f)) (p : Fin n → ℝ)
    (hinf : InfPerturbed (CastZR f) p > ⊥) :
    (ArgMinPerturbed (CastZR f) p).Nonempty := by
  exact p330_core f hic p hinf
