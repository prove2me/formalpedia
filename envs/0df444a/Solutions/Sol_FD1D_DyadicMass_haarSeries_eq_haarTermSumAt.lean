-- Prove2me | solution 1 for FD1D.DyadicMass.haarSeries_eq_haarTermSumAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:15.993225+00:00
-- url     : https://prove2.me/submissions/a5de8f55-2ba9-430d-8dd4-9b01b95abdf0

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_ne_zero_mem_Ioo
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


section
namespace FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace DyadicMass
end DyadicMass
namespace HaarTerm
end HaarTerm
private theorem dyadicTent_eq_zero_of_not_mem_Ioo {l p z : ℝ}
    (hp : 0 < p) (hz : z ∉ Ioo l (l + p)) :
    dyadicTent l p z = 0 := by
  by_contra h
  exact hz (dyadicTent_ne_zero_mem_Ioo hp h)
private theorem dyadicTent_eq_unitTent_affine {a p z : ℝ}
    (hp : 0 < p) (hz0 : a ≤ z) (hz1 : z ≤ a + p) :
    dyadicTent a p z = DyadicMass.unitTent ((z - a) / p) := by
  by_cases hz : z ≤ a + p / 2
  · have hmem : z ∈ Icc a (a + p / 2) := ⟨hz0, hz⟩
    have hnot : z ∉ Ioc (a + p / 2) (a + p) := by
      intro h
      linarith [h.1]
    have hhalf : (z - a) / p ≤ 1 / 2 := by
      apply (div_le_iff₀ hp).2
      linarith
    rw [DyadicMass.unitTent, if_pos hhalf]
    simp [dyadicTent, hmem, hnot]
  · have hnot : z ∉ Icc a (a + p / 2) := by
      intro h
      exact hz h.2
    have hmem : z ∈ Ioc (a + p / 2) (a + p) :=
      ⟨lt_of_not_ge hz, hz1⟩
    have hhalf : ¬(z - a) / p ≤ 1 / 2 := by
      intro h
      have := (div_le_iff₀ hp).1 h
      linarith
    simp only [dyadicTent, Set.indicator_of_notMem hnot,
      Set.indicator_of_mem hmem, zero_add, DyadicMass.unitTent,
      if_neg hhalf]
    field_simp
    ring
private theorem DyadicMass.haarTermSum_haarTermsAt_eq_zero_of_outside
    {L : ℕ} (q : DyadicMass L) {a p z : ℝ} (hp : 0 < p)
    (hz : z ≤ a ∨ a + p ≤ z) :
    haarTermSum (q.haarTermsAt a p) z = 0 := by
  induction q generalizing a p with
  | leaf =>
      simp [haarTermsAt]
  | @branch L l r ihl ihr =>
      have hp2 : 0 < p / 2 := by positivity
      have hroot : dyadicTent a p z = 0 := by
        apply dyadicTent_eq_zero_of_not_mem_Ioo hp
        intro h
        rcases hz with hz | hz <;> linarith [h.1, h.2]
      have hleft : haarTermSum (l.haarTermsAt a (p / 2)) z = 0 := by
        apply ihl hp2
        rcases hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr (by linarith)
      have hright :
          haarTermSum (r.haarTermsAt (a + p / 2) (p / 2)) z = 0 := by
        apply ihr hp2
        rcases hz with hz | hz
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      simp [haarTermsAt, HaarTerm.value, hroot, hleft, hright]
namespace DyadicMass
end DyadicMass
namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
end FiniteLaw
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
namespace DyadicMass
end DyadicMass
namespace MonotoneQuantilePolicy
end MonotoneQuantilePolicy
namespace FiniteLaw
end FiniteLaw
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
namespace DyadicMass
theorem _root_.solution
    {L : ℕ} (q : DyadicMass L) {a p z : ℝ}
    (hp : 0 < p) (hz0 : a ≤ z) (hz1 : z ≤ a + p) :
    q.haarSeries ((z - a) / p) =
      haarTermSum (q.haarTermsAt a p) z := by
  induction q generalizing a p z with
  | leaf =>
      simp [haarSeries, haarTermsAt]
  | @branch L l r ihl ihr =>
      have hp2 : 0 < p / 2 := by positivity
      have hroot :
          dyadicTent a p z = DyadicMass.unitTent ((z - a) / p) :=
        dyadicTent_eq_unitTent_affine hp hz0 hz1
      by_cases hz : z ≤ a + p / 2
      · have hhalf : (z - a) / p ≤ 1 / 2 := by
          apply (div_le_iff₀ hp).2
          linarith
        have hcoord : 2 * ((z - a) / p) = (z - a) / (p / 2) := by
          field_simp
        have hactive :
            l.haarSeries (2 * ((z - a) / p)) =
              haarTermSum (l.haarTermsAt a (p / 2)) z := by
          rw [hcoord]
          exact ihl hp2 hz0 hz
        have hinactive :
            haarTermSum (r.haarTermsAt (a + p / 2) (p / 2)) z = 0 :=
          r.haarTermSum_haarTermsAt_eq_zero_of_outside hp2 (Or.inl hz)
        rw [DyadicMass.haarSeries]
        simp only [hhalf, if_pos]
        rw [hactive]
        simp [haarTermsAt, HaarTerm.value, hroot, hinactive]
      · have hhalf : ¬(z - a) / p ≤ 1 / 2 := by
          intro h
          have := (div_le_iff₀ hp).1 h
          linarith
        have hzmid : a + p / 2 ≤ z := le_of_not_ge hz
        have hcoord :
            2 * ((z - a) / p) - 1 =
              (z - (a + p / 2)) / (p / 2) := by
          field_simp
          ring
        have hactive :
            r.haarSeries (2 * ((z - a) / p) - 1) =
              haarTermSum
                (r.haarTermsAt (a + p / 2) (p / 2)) z := by
          rw [hcoord]
          apply ihr hp2 hzmid
          linarith
        have hinactive :
            haarTermSum (l.haarTermsAt a (p / 2)) z = 0 :=
          l.haarTermSum_haarTermsAt_eq_zero_of_outside hp2
            (Or.inr hzmid)
        rw [DyadicMass.haarSeries]
        simp only [hhalf]
        rw [hactive]
        simp [haarTermsAt, HaarTerm.value, hroot, hinactive]
end DyadicMass
end FD1D
