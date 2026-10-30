-- Prove2me | solution 1 for BoxTDIMinMax.Separable.claim_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:05:31.55432+00:00
-- url     : https://prove2.me/submissions/09064ae8-cb9e-4fb6-af5b-b24a79fbafdb

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

open Matrix BoxTDIMinMax.Separable

theorem solution {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (phi : S → ℤ → WithTop ℤ) (hphi : ∀ s, DiscConvex (phi s))
    (Q : Matrix ι S ℤ) (p : ι → ℤ)
    (hfin : ∀ z ∈ intPts Q p, Phi phi z ≠ ⊤)
    (zStar : S → ℤ) (hz : zStar ∈ intPts Q p)
    (hmin : ∀ z ∈ intPts Q p, Phi phi zStar ≤ Phi phi z) :
    Cond29 Q p zStar (fun s => lowerSlope (phi s) (zStar s))
      (fun s => upperSlope (phi s) (zStar s)) := by
  have untop : ∀ x : WithTop ℤ, x ≠ ⊤ → ((x.untopD 0 : ℤ) : WithTop ℤ) = x := by
    intro x hx
    obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
    rfl
  have esum : ∀ (T : Finset S) (g : S → ℤ),
      ∑ s ∈ T, (((g s : ℤ) : ℝ) : EReal) = (((∑ s ∈ T, g s : ℤ) : ℝ) : EReal) := by
    intro T g
    induction T using Finset.induction_on with
    | empty => simp
    | insert x T hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, ih]
      push_cast
      rfl
  intro Sm Sp hdisj hz'
  set z' : S → ℤ := zStar + chi Sp - chi Sm with hz'def
  have hz's : ∀ s, z' s = if s ∈ Sp then zStar s + 1 else if s ∈ Sm then zStar s - 1
      else zStar s := by
    intro s
    simp only [hz'def, Pi.add_apply, Pi.sub_apply, chi]
    by_cases h1 : s ∈ Sp
    · have h2 : s ∉ Sm := fun h => Finset.disjoint_left.mp hdisj h h1
      simp [h1, h2]
    · by_cases h2 : s ∈ Sm <;> simp [h1, h2]
  have fin0 : ∀ s, phi s (zStar s) ≠ ⊤ := fun s =>
    WithTop.sum_ne_top.mp (hfin zStar hz) s (Finset.mem_univ s)
  have fin' : ∀ s, phi s (z' s) ≠ ⊤ := fun s =>
    WithTop.sum_ne_top.mp (hfin z' hz') s (Finset.mem_univ s)
  set a : S → ℤ := fun s => (phi s (zStar s)).untopD 0 with ha
  set f : S → ℤ := fun s => (phi s (z' s)).untopD 0 with hf
  have hPhi0 : Phi phi zStar = ((∑ s, a s : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_sum]; unfold Phi
    exact Finset.sum_congr rfl (fun s _ => (untop _ (fin0 s)).symm)
  have hPhi' : Phi phi z' = ((∑ s, f s : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_sum]; unfold Phi
    exact Finset.sum_congr rfl (fun s _ => (untop _ (fin' s)).symm)
  have hle : ∑ s, a s ≤ ∑ s, f s := by
    have := hmin z' hz'
    rw [hPhi0, hPhi'] at this
    exact_mod_cast this
  -- the left sum
  have hlo : ∑ s ∈ Sm, lowerSlope (phi s) (zStar s) =
      (((∑ s ∈ Sm, (a s - f s) : ℤ) : ℝ) : EReal) := by
    rw [← esum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have h1 : s ∉ Sp := fun h => Finset.disjoint_left.mp hdisj hs h
    have hzs : z' s = zStar s - 1 := by rw [hz's s]; simp [h1, hs]
    unfold lowerSlope
    have hne : phi s (zStar s - 1) ≠ ⊤ := by rw [← hzs]; exact fin' s
    rw [if_neg hne]
    simp only [ha, hf, hzs]
  have hup : ∑ s ∈ Sp, upperSlope (phi s) (zStar s) =
      (((∑ s ∈ Sp, (f s - a s) : ℤ) : ℝ) : EReal) := by
    rw [← esum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hzs : z' s = zStar s + 1 := by rw [hz's s]; simp [hs]
    unfold upperSlope
    have hne : phi s (zStar s + 1) ≠ ⊤ := by rw [← hzs]; exact fin' s
    rw [if_neg hne]
    simp only [ha, hf, hzs]
  show ∑ s ∈ Sm, lowerSlope (phi s) (zStar s) ≤ ∑ s ∈ Sp, upperSlope (phi s) (zStar s)
  rw [hlo, hup]
  -- integer inequality
  have hout : ∀ s ∈ Finset.univ, s ∉ Sp ∪ Sm → f s - a s = 0 := by
    intro s _ hs
    rw [Finset.mem_union, not_or] at hs
    have : z' s = zStar s := by rw [hz's s]; simp [hs.1, hs.2]
    simp only [hf, ha, this, sub_self]
  have htot : ∑ s, (f s - a s) = ∑ s ∈ Sp, (f s - a s) + ∑ s ∈ Sm, (f s - a s) := by
    rw [← Finset.sum_union hdisj.symm]
    exact (Finset.sum_subset (Finset.subset_univ _) hout).symm
  have hsub : ∑ s, (f s - a s) = ∑ s, f s - ∑ s, a s := Finset.sum_sub_distrib _ _
  have hsm : ∑ s ∈ Sm, (a s - f s) = -∑ s ∈ Sm, (f s - a s) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun s _ => by ring)
  have hint : ∑ s ∈ Sm, (a s - f s) ≤ ∑ s ∈ Sp, (f s - a s) := by linarith
  exact_mod_cast hint
