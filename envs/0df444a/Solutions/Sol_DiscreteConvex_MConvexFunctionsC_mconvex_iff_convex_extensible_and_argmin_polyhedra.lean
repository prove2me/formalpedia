-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsC.mconvex_iff_convex_extensible_and_argmin_polyhedra
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T19:49:15.362869+00:00
-- url     : https://prove2.me/submissions/492f9571-7b5e-46c6-b97f-2b0808849d0f

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MConvexPolyhedron
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatConvexPolyhedron
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_CCWeight

set_option autoImplicit false

namespace DP948369b5
open DiscreteConvex.MConvexFunctionsC

/-- The admissible points: the two parallel lines `x 0 = 0` and `x 0 = 1` of the plane `x(V) = 0`. -/
def Adm (x : Fin 3 → ℤ) : Prop := x 0 + x 1 + x 2 = 0 ∧ (x 0 = 0 ∨ x 0 = 1)

/-- Counterexample: `x 1` on the line `x 0 = 0`, `-x 1` on the line `x 0 = 1`. -/
noncomputable def g (x : Fin 3 → ℤ) : WithTop ℝ :=
  open Classical in
  if Adm x then (((x 1 : ℝ) - 2 * (x 0 : ℝ) * (x 1 : ℝ) : ℝ) : WithTop ℝ) else ⊤

lemma g_adm {x : Fin 3 → ℤ} (h : Adm x) :
    g x = (((x 1 : ℝ) - 2 * (x 0 : ℝ) * (x 1 : ℝ) : ℝ) : WithTop ℝ) := by
  unfold g; rw [if_pos h]

lemma g_nadm {x : Fin 3 → ℤ} (h : ¬ Adm x) : g x = ⊤ := by
  unfold g; rw [if_neg h]

lemma mem_dom {x : Fin 3 → ℤ} : x ∈ DomZ g ↔ Adm x := by
  unfold DomZ
  show g x ≠ ⊤ ↔ Adm x
  by_cases h : Adm x
  · rw [g_adm h]; exact iff_of_true WithTop.coe_ne_top h
  · rw [g_nadm h]; exact iff_of_false (fun h' => h' rfl) h

/-- The key computation: every convex representation of an admissible point gives the same value. -/
lemma rep_value (z : Fin 3 → ℤ) (hz : Adm z) (S : Finset (Fin 3 → ℤ)) (lam : (Fin 3 → ℤ) → ℝ)
    (hl0 : ∀ y ∈ S, 0 ≤ lam y) (hl1 : ∑ y ∈ S, lam y = 1) (hS : ∀ y ∈ S, y ∈ DomZ g)
    (hrep : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = (z v : ℝ)) :
    ∑ y ∈ S, lam y * (g y).untopD 0 = (z 1 : ℝ) - 2 * (z 0 : ℝ) * (z 1 : ℝ) := by
  have hA : ∀ y ∈ S, Adm y := fun y hy => mem_dom.mp (hS y hy)
  have hval : ∀ y ∈ S, (g y).untopD 0 = (y 1 : ℝ) - 2 * (y 0 : ℝ) * (y 1 : ℝ) := by
    intro y hy; rw [g_adm (hA y hy)]; rfl
  -- each `lam y * y 0 = a * lam y` where `a = z 0`
  have hkey : ∀ y ∈ S, lam y * (y 0 : ℝ) = (z 0 : ℝ) * lam y := by
    rcases hz.2 with h0 | h1
    · have hsum : ∑ y ∈ S, lam y * (y 0 : ℝ) = 0 := by rw [hrep 0, h0]; simp
      have hnn : ∀ y ∈ S, 0 ≤ lam y * (y 0 : ℝ) := by
        intro y hy
        rcases (hA y hy).2 with e | e <;> simp [e, hl0 y hy]
      intro y hy
      rw [(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum y hy, h0]; simp
    · have hsum : ∑ y ∈ S, lam y * (1 - (y 0 : ℝ)) = 0 := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hl1, hrep 0, h1]; simp
      have hnn : ∀ y ∈ S, 0 ≤ lam y * (1 - (y 0 : ℝ)) := by
        intro y hy
        rcases (hA y hy).2 with e | e <;> simp [e, hl0 y hy]
      intro y hy
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum y hy
      rw [h1]; push_cast; linarith [this, mul_sub (lam y) 1 (y 0 : ℝ)]
  calc ∑ y ∈ S, lam y * (g y).untopD 0
      = ∑ y ∈ S, (lam y * (y 1 : ℝ) - 2 * (lam y * (y 0 : ℝ)) * (y 1 : ℝ)) := by
        apply Finset.sum_congr rfl; intro y hy; rw [hval y hy]; ring
    _ = ∑ y ∈ S, (lam y * (y 1 : ℝ) - 2 * (z 0 : ℝ) * (lam y * (y 1 : ℝ))) := by
        apply Finset.sum_congr rfl; intro y hy; rw [hkey y hy]; ring
    _ = (z 1 : ℝ) - 2 * (z 0 : ℝ) * (z 1 : ℝ) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hrep 1]

/-- Any represented point is admissible. -/
lemma rep_adm (z : Fin 3 → ℤ) (S : Finset (Fin 3 → ℤ)) (lam : (Fin 3 → ℤ) → ℝ)
    (hl0 : ∀ y ∈ S, 0 ≤ lam y) (hl1 : ∑ y ∈ S, lam y = 1) (hS : ∀ y ∈ S, y ∈ DomZ g)
    (hrep : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = (z v : ℝ)) : Adm z := by
  have hA : ∀ y ∈ S, Adm y := fun y hy => mem_dom.mp (hS y hy)
  refine ⟨?_, ?_⟩
  · have : ((z 0 + z 1 + z 2 : ℤ) : ℝ) = 0 := by
      push_cast
      rw [← hrep 0, ← hrep 1, ← hrep 2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro y hy
      have e := (hA y hy).1
      have e' : ((y 0 : ℝ) + y 1 + y 2) = 0 := by exact_mod_cast e
      rw [← mul_add, ← mul_add, e', mul_zero]
    exact_mod_cast this
  · have hlo : (0 : ℝ) ≤ z 0 := by
      rw [← hrep 0]
      apply Finset.sum_nonneg; intro y hy
      rcases (hA y hy).2 with e | e <;> simp [e, hl0 y hy]
    have hhi : (z 0 : ℝ) ≤ 1 := by
      rw [← hrep 0, ← hl1]
      apply Finset.sum_le_sum; intro y hy
      rcases (hA y hy).2 with e | e <;> simp [e, hl0 y hy]
    have h1 : (0 : ℤ) ≤ z 0 := by exact_mod_cast hlo
    have h2 : z 0 ≤ 1 := by exact_mod_cast hhi
    omega

lemma inner_ge (z : Fin 3 → ℤ) (hz : Adm z) (S : Finset (Fin 3 → ℤ)) (hS : ∀ y ∈ S, y ∈ DomZ g) :
    (((z 1 : ℝ) - 2 * (z 0 : ℝ) * (z 1 : ℝ) : ℝ) : WithTop ℝ) ≤
      ConvexClosureValOn g S (fun v => (z v : ℝ)) := by
  unfold ConvexClosureValOn
  set T := {L : WithTop ℝ | ∃ lam : (Fin 3 → ℤ) → ℝ,
    (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ g) ∧
    (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = (fun v => (z v : ℝ)) v) ∧
    L = ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)} with hT
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he, WithTop.sInf_empty]; exact le_top
  · apply le_csInf hne
    rintro L ⟨lam, hl0, hl1, hS', hrep, rfl⟩
    rw [rep_value z hz S lam hl0 hl1 hS' hrep]

lemma inner_single (z : Fin 3 → ℤ) (hz : Adm z) :
    ConvexClosureValOn g {z} (fun v => (z v : ℝ)) =
      (((z 1 : ℝ) - 2 * (z 0 : ℝ) * (z 1 : ℝ) : ℝ) : WithTop ℝ) := by
  apply le_antisymm _ (inner_ge z hz {z} (by simpa [mem_dom] using hz))
  unfold ConvexClosureValOn
  apply csInf_le
  · refine ⟨(((z 1 : ℝ) - 2 * (z 0 : ℝ) * (z 1 : ℝ) : ℝ) : WithTop ℝ), ?_⟩
    rintro L ⟨lam, hl0, hl1, hS', hrep, rfl⟩
    rw [rep_value z hz {z} lam hl0 hl1 hS' hrep]
  · refine ⟨fun _ => 1, by simp, by simp, by simpa [mem_dom] using hz, by simp, ?_⟩
    rw [Finset.sum_singleton, one_mul, g_adm hz]; rfl

lemma closure_adm (z : Fin 3 → ℤ) (hz : Adm z) :
    ConvexClosureVal g (fun v => (z v : ℝ)) = g z := by
  rw [g_adm hz]
  unfold ConvexClosureVal
  apply le_antisymm
  · apply csInf_le
    · refine ⟨(((z 1 : ℝ) - 2 * (z 0 : ℝ) * (z 1 : ℝ) : ℝ) : WithTop ℝ), ?_⟩
      rintro L ⟨S, hS, rfl⟩
      exact inner_ge z hz S hS
    · exact ⟨{z}, by simpa [mem_dom] using hz, (inner_single z hz).symm⟩
  · refine le_csInf ⟨ConvexClosureValOn g {z} (fun v => (z v : ℝ)), {z},
      by simpa [mem_dom] using hz, rfl⟩ ?_
    rintro L ⟨S, hS, rfl⟩
    exact inner_ge z hz S hS

lemma closure_nadm (z : Fin 3 → ℤ) (hz : ¬ Adm z) :
    ConvexClosureVal g (fun v => (z v : ℝ)) = ⊤ := by
  have hin : ∀ S : Finset (Fin 3 → ℤ), ConvexClosureValOn g S (fun v => (z v : ℝ)) = ⊤ := by
    intro S
    unfold ConvexClosureValOn
    convert WithTop.sInf_empty (α := ℝ)
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨lam, hl0, hl1, hS', hrep, -⟩
    exact hz (rep_adm z S lam hl0 hl1 hS' hrep)
  unfold ConvexClosureVal
  set T := {L : WithTop ℝ | ∃ (S : Finset (Fin 3 → ℤ)),
    (∀ y ∈ S, y ∈ DomZ g) ∧ L = ConvexClosureValOn g S (fun v => (z v : ℝ))}
  rcases T.eq_empty_or_nonempty with he | hne
  · rw [he, WithTop.sInf_empty]
  · apply le_antisymm le_top
    apply le_csInf hne
    rintro L ⟨S, -, rfl⟩
    rw [hin S]

lemma g_ext : ConvexExtensible g := by
  intro z
  by_cases hz : Adm z
  · exact closure_adm z hz
  · rw [closure_nadm z hz, g_nadm hz]

lemma ccw_adm (p : Fin 3 → ℝ) (z : Fin 3 → ℤ) (hz : Adm z) :
    CCWeight g p (fun v => (z v : ℝ)) =
      (((z 1 : ℝ) - 2 * (z 0 : ℝ) * (z 1 : ℝ) - ∑ v, p v * (z v : ℝ) : ℝ) : WithTop ℝ) := by
  unfold CCWeight
  rw [closure_adm z hz, g_adm hz, ← WithTop.coe_add]
  ring_nf

lemma argmin_empty (p : Fin 3 → ℝ) : ¬ (ArgMinOn (CCWeight g p)).Nonempty := by
  rintro ⟨x, hx⟩
  have hx' : ∀ z : Fin 3 → ℤ, Adm z →
      CCWeight g p x ≤ (((z 1 : ℝ) - 2 * (z 0 : ℝ) * (z 1 : ℝ) - ∑ v, p v * (z v : ℝ) : ℝ) :
        WithTop ℝ) := by
    intro z hz
    rw [← ccw_adm p z hz]
    exact hx _
  -- the value at `x` is finite
  have hfin := hx' ![0, 0, 0] (by simp [Adm])
  obtain ⟨r, hr⟩ : ∃ r : ℝ, CCWeight g p x = (r : WithTop ℝ) := by
    cases h : CCWeight g p x with
    | top => rw [h] at hfin; exact absurd hfin (not_le.mpr (WithTop.coe_lt_top _))
    | coe r => exact ⟨r, rfl⟩
  have line0 : ∀ k : ℤ, r ≤ (k : ℝ) * (1 - (p 1 - p 2)) := by
    intro k
    have := hx' ![0, k, -k] (by simp [Adm])
    rw [hr, WithTop.coe_le_coe] at this
    simp [Fin.sum_univ_three] at this
    linarith
  have line1 : ∀ k : ℤ, r ≤ (p 2 - p 0) - (k : ℝ) * (1 + (p 1 - p 2)) := by
    intro k
    have := hx' ![1, k, -1 - k] (by simp [Adm])
    rw [hr, WithTop.coe_le_coe] at this
    simp [Fin.sum_univ_three] at this
    linarith
  obtain ⟨n, hn⟩ := exists_int_gt (|r| + |p 2 - p 0| + 1)
  have hr1 := le_abs_self r
  have hr2 := neg_abs_le r
  have hc := le_abs_self (p 2 - p 0)
  have hn0 : (0 : ℝ) < n := by linarith [abs_nonneg r, abs_nonneg (p 2 - p 0)]
  rcases le_or_gt (p 1 - p 2) 0 with hd | hd
  · have := line0 (-n)
    have e : ((-n : ℤ) : ℝ) * (1 - (p 1 - p 2)) = -(n : ℝ) + (n : ℝ) * (p 1 - p 2) := by
      push_cast; ring
    rw [e] at this
    linarith [mul_nonpos_of_nonneg_of_nonpos hn0.le hd, abs_nonneg r, abs_nonneg (p 2 - p 0)]
  · have := line1 n
    have e : (p 2 - p 0) - (n : ℝ) * (1 + (p 1 - p 2)) =
        (p 2 - p 0) - (n : ℝ) - (n : ℝ) * (p 1 - p 2) := by ring
    rw [e] at this
    linarith [mul_pos hn0 hd, abs_nonneg r, abs_nonneg (p 2 - p 0)]

lemma not_mexch : ¬ MExchangeAxiom g := by
  intro h
  have hx : (![0, -1, 1] : Fin 3 → ℤ) ∈ DomZ g := mem_dom.mpr (by simp [Adm])
  have hy : (![1, 0, -1] : Fin 3 → ℤ) ∈ DomZ g := mem_dom.mpr (by simp [Adm])
  obtain ⟨v, hv, hle⟩ := h _ hx _ hy 2 (by simp [SuppPos])
  have hv' : v = 0 ∨ v = 1 := by
    simp [SuppNeg] at hv
    revert hv; fin_cases v <;> simp
  have gx : g ![0, -1, 1] = ((-1 : ℝ) : WithTop ℝ) := by rw [g_adm (by simp [Adm])]; norm_num
  have gy : g ![1, 0, -1] = ((0 : ℝ) : WithTop ℝ) := by rw [g_adm (by simp [Adm])]; norm_num
  have ga : g ![1, -1, 0] = ((1 : ℝ) : WithTop ℝ) := by rw [g_adm (by simp [Adm])]; norm_num
  have gb : g ![0, 0, 0] = ((0 : ℝ) : WithTop ℝ) := by rw [g_adm (by simp [Adm])]; norm_num
  rcases hv' with rfl | rfl
  · have e1 : (fun w => (![0, -1, 1] : Fin 3 → ℤ) w - CharVec 2 w + CharVec 0 w) = ![1, -1, 0] := by
      funext w; fin_cases w <;> decide
    have e2 : (fun w => (![1, 0, -1] : Fin 3 → ℤ) w + CharVec 2 w - CharVec 0 w) = ![0, 0, 0] := by
      funext w; fin_cases w <;> decide
    rw [e1, e2, ga, gb, gx, gy, ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le,
      WithTop.coe_le_coe] at hle
    norm_num at hle
  · have e1 : (fun w => (![0, -1, 1] : Fin 3 → ℤ) w - CharVec 2 w + CharVec 1 w) = ![0, 0, 0] := by
      funext w; fin_cases w <;> decide
    have e2 : (fun w => (![1, 0, -1] : Fin 3 → ℤ) w + CharVec 2 w - CharVec 1 w) = ![1, -1, 0] := by
      funext w; fin_cases w <;> decide
    rw [e1, e2, ga, gb, gx, gy, ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le,
      WithTop.coe_le_coe] at hle
    norm_num at hle

theorem cex : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hdom : (DomZ f).Nonempty),
    (MExchangeAxiom f ↔
      (ConvexExtensible f ∧ ∀ p : V → ℝ, (ArgMinOn (CCWeight f p)).Nonempty →
        MConvexPolyhedron (ArgMinOn (CCWeight f p)))) ∧
    (MNaturalConvex f ↔
      (ConvexExtensible f ∧ ∀ p : V → ℝ, (ArgMinOn (CCWeight f p)).Nonempty →
        MNatConvexPolyhedron (ArgMinOn (CCWeight f p))))) := by
  intro h
  have hdom : (DomZ g).Nonempty := ⟨![0, 0, 0], mem_dom.mpr (by simp [Adm])⟩
  exact not_mexch ((h (V := Fin 3) g hdom).1.mpr
    ⟨g_ext, fun p hp => absurd hp (argmin_empty p)⟩)

end DP948369b5

open DiscreteConvex.MConvexFunctionsC in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hdom : (DomZ f).Nonempty),
    (MExchangeAxiom f ↔
      (ConvexExtensible f ∧ ∀ p : V → ℝ, (ArgMinOn (CCWeight f p)).Nonempty →
        MConvexPolyhedron (ArgMinOn (CCWeight f p)))) ∧
    (MNaturalConvex f ↔
      (ConvexExtensible f ∧ ∀ p : V → ℝ, (ArgMinOn (CCWeight f p)).Nonempty →
        MNatConvexPolyhedron (ArgMinOn (CCWeight f p))))) := by
  exact DP948369b5.cex

