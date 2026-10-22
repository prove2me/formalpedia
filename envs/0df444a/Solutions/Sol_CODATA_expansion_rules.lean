-- Prove2me | solution 1 for CODATA.expansion_rules
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:08:02.817861+00:00
-- url     : https://prove2.me/submissions/033dc9a4-b160-47b0-b4f4-9c94b5b9fb15

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values
/-!
# Expansion of uncertainties preserves correlations

Section XII of the 2022 CODATA report applies expansion factors to the
uncertainties of groups of input data (1.7 and 2.5 in the main
adjustment; 3.9 for the sixteen values of the Newtonian constant of
gravitation) in order to reduce all normalized residuals to two or
less, and it states that the factors are applied to all the data of a
group so as to maintain their original relative weights and
correlations. This milestone formalizes the underlying algebra of the
covariance matrix under such an expansion: the expanded covariance is
the entrywise product by the pairwise products of the factors; a common
factor leaves every correlation coefficient unchanged; and more
generally the correlation coefficient of a pair is unchanged whenever
the two members carry equal factors. The constant factor 39/10 is the
expansion factor 3.9 of the separate adjustment of the Newtonian
constant of gravitation. This milestone is proved on the way to the
goal theorem `CODATA.codata_self_consistent`.
-/

open CODATA

/-- Let V be a covariance matrix with positive diagonal entries and fs
a family of positive factors. The expansion of V by the constant
factor 39/10 multiplies every entry by (39/10)^2; every correlation
coefficient of V is unchanged by that expansion; and more generally,
whenever two entries carry equal factors, their correlation
coefficient is unchanged by the expansion. -/
theorem solution {N : ℕ} (V : Matrix (Fin N) (Fin N) ℝ)
    (fs : Fin N → ℝ) (hfs : ∀ k, 0 < fs k) (hV : ∀ k, 0 < V k k) :
    (∀ k l, expandD (fun _ => 39/10) V k l = (39/10) * (39/10) * V k l) ∧
      (∀ i j, corr (expandD (fun _ => 39/10) V) i j = corr V i j) ∧
      (∀ i j, fs i = fs j → corr (expandD fs V) i j = corr V i j) := by
  refine ⟨fun k l => by simp [expandD], ?_, ?_⟩
  · intro i j
    simp only [corr, expandD, Matrix.of_apply]
    have hi := hV i; have hj := hV j
    have : (39/10:ℝ) * (39/10) * V i i * ((39/10) * (39/10) * V j j)
        = ((39/10) * (39/10))^2 * (V i i * V j j) := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have : 0 < Real.sqrt (V i i * V j j) := Real.sqrt_pos.2 (by positivity)
    field_simp
  · intro i j hij
    simp only [corr, expandD, Matrix.of_apply]
    have hi := hV i; have hj := hV j; have hf := hfs i
    rw [← hij]
    have : fs i * fs i * V i i * (fs i * fs i * V j j)
        = (fs i * fs i)^2 * (V i i * V j j) := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have : 0 < Real.sqrt (V i i * V j j) := Real.sqrt_pos.2 (by positivity)
    field_simp


