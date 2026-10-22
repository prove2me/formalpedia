-- Prove2me | solution 1 for CODATA.weighted_mean
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:13:00.980979+00:00
-- url     : https://prove2.me/submissions/62684808-4082-4a6d-bc78-ff5c92048798

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

open CODATA

/-!
# The single adjusted constant: the weighted mean

The 2022 CODATA report treats the Newtonian constant of gravitation
separately: an adjustment of sixteen input data for a single adjusted
constant (sixteen minus one equals fifteen degrees of freedom), with
an expansion factor of 3.9 applied to the uncertainties of all the
data. This milestone identifies the general rank-one case of the
least-squares model of `Def_CODATA_lsa`: when every observational
equation reads y i = x + 0, the adjusted constant is the weighted mean
of the data, the weights being the entries of the weight matrix; its
variance is the single entry of the inverse of the normal matrix; and
the adjusted value is unique. This milestone is proved on the way to
the goal theorem `CODATA.codata_self_consistent`.
-/

open CODATA
/-- For a least-squares problem with one adjusted constant, at least
one input datum, zero offsets, observational equations y i = x and a
strictly positive definite weight matrix, the adjusted constant at a
solution x of the normal equations is the weighted mean
(sum_i sum_j G i j y j) / (sum_i sum_j G i j); there is a two-sided
inverse C of the normal matrix, the variance of the adjusted constant
is its (0, 0) entry, 1 / (sum_i sum_j G i j); and every other solution
of the normal equations has the same value. -/
theorem solution {N : ℕ} (L : LSQ N 1) (hN : 0 < N)
    (hG : IsSPD L.G) (hA : ∀ i, L.A i 0 = 1) (hb : ∀ i, L.b i = 0)
    (x : Fin 1 → ℝ) (hx : SolvesNormal L x) :
    x 0 = (∑ i, ∑ j, L.G i j * L.y j) / (∑ i, ∑ j, L.G i j) ∧
      ∃ C, IsCov L C ∧ C 0 0 = 1 / (∑ i, ∑ j, L.G i j) ∧
        ∀ z, SolvesNormal L z → z 0 = x 0 := by
  have hS : 0 < ∑ i, ∑ j, L.G i j := by
    have hv : (fun _ : Fin N => (1:ℝ)) ≠ 0 := by
      intro h; have := congrFun h ⟨0, hN⟩; simp at this
    have := hG.2 _ hv
    simpa using this
  have hres : ∀ (z : Fin 1 → ℝ) j, resid L z j = L.y j - z 0 := by
    intro z j; simp [resid, Matrix.mulVec, dotProduct, hA, hb]
  have hsol : ∀ z, SolvesNormal L z → z 0 = (∑ i, ∑ j, L.G i j * L.y j) / (∑ i, ∑ j, L.G i j) := by
    intro z hz
    have h := hz 0
    simp only [hA, hres, one_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
    rw [eq_div_iff hS.ne']; linarith
  refine ⟨hsol x hx, fun _ _ => 1 / (∑ i, ∑ j, L.G i j), ?_, rfl,
    fun z hz => by rw [hsol z hz, hsol x hx]⟩
  · constructor
    · intro k l
      have hk : k = 0 := Subsingleton.elim _ _
      have hl : l = 0 := Subsingleton.elim _ _
      subst hk hl
      simp [normalMat, hA]; field_simp
    · intro k l
      have hk : k = 0 := Subsingleton.elim _ _
      have hl : l = 0 := Subsingleton.elim _ _
      subst hk hl
      simp [normalMat, hA]; field_simp


