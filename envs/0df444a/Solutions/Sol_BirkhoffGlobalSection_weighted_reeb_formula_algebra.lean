-- Prove2me | solution 1 for BirkhoffGlobalSection.weighted_reeb_formula_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:39:29.350299+00:00
-- url     : https://prove2.me/submissions/c2237f3e-f7a2-4103-be93-b726e463e99a

import Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_contact_geometry
import Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_weight
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false




set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution (u : Phase) (hu : u ∈ unitThreeSphere)
    (a : ℝ) (ha : 0 < a) (L : Phase →L[ℝ] ℝ) :
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let g : Phase := fun i => L (coordinateVector i)
    let R : Phase := (a ^ 2)⁻¹ • ((2 * a + L u) • J u - J g - L (J u) • u)
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
      a * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        L R * phaseRadialContact u w - L w * phaseRadialContact u R -
          a * phaseSymplecticForm R w = 0) := by
  have coordinateExpansion (L : Phase →L[ℝ] ℝ) (v : Phase) :
      L v = v 0 * L (coordinateVector 0) + v 1 * L (coordinateVector 1) +
        v 2 * L (coordinateVector 2) + v 3 * L (coordinateVector 3) := by
    have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
        v 2 • coordinateVector 2 + v 3 • coordinateVector 3 := by
      ext i
      fin_cases i <;> simp [coordinateVector]
    calc
      L v = L (v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
        v 2 • coordinateVector 2 + v 3 • coordinateVector 3) := congrArg L hv
      _ = _ := by simp
  let D : Phase → Phase → ℝ := fun v w =>
    v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3
  let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
  let g : Phase := fun i => L (coordinateVector i)
  have hgrad (v : Phase) : D g v = L v := by
    rw [coordinateExpansion L v]
    dsimp [D, g]
    ring
  have hunit : D u u = 1 := by
    have hQ : zNormSq u + wNormSq u = 1 := hu
    dsimp [D]
    simp [zNormSq, wNormSq] at hQ
    nlinarith [hQ]
  have horth (v : Phase) : D v (J v) = 0 := by simp [D, J]; ring
  have hswap (v w : Phase) : D v (J w) = -D (J v) w := by simp [D, J]; ring
  have hωJ (v w : Phase) : phaseSymplecticForm (J v) w = D v w := by
    simp [D, J, phaseSymplecticForm]
    ring
  have hαJ (v : Phase) : phaseRadialContact u (J v) = D v u / 2 := by
    simp [D, J, phaseRadialContact, phaseSymplecticForm]
    ring
  have hαself : phaseRadialContact u u = 0 := by
    simp [phaseRadialContact, phaseSymplecticForm]
    ring
  have hLJg : L (J g) = 0 := by rw [← hgrad, horth]
  let V : Phase := (2 * a + L u) • J u - J g - L (J u) • u
  have htV : D u V = 0 := by
    have heq : D u V = (2 * a + L u) * D u (J u) -
        D u (J g) - L (J u) * D u u := by
      simp [D, V]
      ring
    rw [heq, horth, hswap]
    have hg : D (J u) g = L (J u) := by rw [← hgrad]; dsimp [D]; ring
    rw [hg, hunit]
    ring
  have hαV : phaseRadialContact u V = a := by
    have heq : phaseRadialContact u V =
        (2 * a + L u) * phaseRadialContact u (J u) -
          phaseRadialContact u (J g) - L (J u) * phaseRadialContact u u := by
      simp [V, phaseRadialContact, phaseSymplecticForm]
      ring
    rw [heq, hαJ, hαJ, hunit, hgrad, hαself]
    ring
  have hLV : L V = 2 * a * L (J u) := by
    simp only [V, map_sub, map_smul, smul_eq_mul]
    rw [hLJg]
    ring
  have hωV (w : Phase) (hw : D u w = 0) :
      phaseSymplecticForm V w = -L w + 2 * L (J u) * phaseRadialContact u w := by
    have heq : phaseSymplecticForm V w =
        (2 * a + L u) * phaseSymplecticForm (J u) w -
          phaseSymplecticForm (J g) w - L (J u) * phaseSymplecticForm u w := by
      simp [V, phaseSymplecticForm]
      ring
    rw [heq, hωJ, hωJ, hw, hgrad]
    simp [phaseRadialContact]
    ring
  let R : Phase := (a ^ 2)⁻¹ • V
  have hαR : phaseRadialContact u R = (a ^ 2)⁻¹ * a := by
    have heq : phaseRadialContact u R = (a ^ 2)⁻¹ * phaseRadialContact u V := by
      simp [R, phaseRadialContact, phaseSymplecticForm]
      ring
    rw [heq, hαV]
  change (D u R = 0) ∧ (a * phaseRadialContact u R = 1) ∧
    (∀ w : Phase, D u w = 0 →
      L R * phaseRadialContact u w - L w * phaseRadialContact u R -
        a * phaseSymplecticForm R w = 0)
  refine ⟨?_, ?_, ?_⟩
  · have heq : D u R = (a ^ 2)⁻¹ * D u V := by simp [D, R]; ring
    rw [heq, htV, mul_zero]
  · rw [hαR]
    field_simp [ha.ne']
  · intro w hw
    have hωR : phaseSymplecticForm R w = (a ^ 2)⁻¹ * phaseSymplecticForm V w := by
      simp [R, phaseSymplecticForm]
      ring
    have hLR : L R = (a ^ 2)⁻¹ * L V := by simp [R]
    rw [hLR, hLV, hαR, hωR, hωV w hw]
    ring
