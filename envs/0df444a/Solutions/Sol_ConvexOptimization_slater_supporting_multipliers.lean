-- Prove2me | solution 1 for ConvexOptimization.slater_supporting_multipliers
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-14T14:51:56.980714+00:00
-- url     : https://prove2.me/submissions/3da6eecf-8e4a-42af-9f65-ca743a7b75d0

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal Topology
open MeasureTheory
open Filter

private theorem slaterEqualityCoordinates_surjective {n p : ℕ}
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a) :
    Function.Surjective (fun x : EuclideanSpace ℝ (Fin n) => (fun j => ⟪a j, x⟫)) := by
  let e : EuclideanSpace ℝ (Fin p) ≃ₗ[ℝ] (Fin p → ℝ) :=
    WithLp.linearEquiv 2 ℝ (Fin p → ℝ)
  let S : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (Fintype.linearCombination ℝ a).comp e.toLinearMap
  have hSinj : Function.Injective S :=
    ha.fintypeLinearCombination_injective.comp e.injective
  have hSrank : Module.finrank ℝ S.range = p := by
    have hr := S.finrank_range_add_finrank_ker
    rw [LinearMap.ker_eq_bot.mpr hSinj] at hr
    simpa using hr
  have hSadjsurj : Function.Surjective S.adjoint := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_adjoint, hSrank]
    simp
  intro v
  obtain ⟨x, hx⟩ := hSadjsurj (WithLp.toLp 2 v)
  refine ⟨x, ?_⟩
  funext j
  have hinner := S.adjoint_inner_right (EuclideanSpace.basisFun (Fin p) ℝ j) x
  simpa [hx, S, e, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
    Fintype.linearCombination_apply] using hinner.symm

theorem solution {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs_ineq : ∀ i, fc i xs < 0)
    (hxs_eq : ∀ j, ⟪a j, xs⟫ = b j)
    (hbdd : BddBelow (f₀ '' ConvexOptimization.feasibleSet fc a b)) :
    ∃ (lam : Fin mm → ℝ) (nu : Fin p → ℝ), (∀ i, 0 ≤ lam i) ∧
      ∀ x, sInf (f₀ '' ConvexOptimization.feasibleSet fc a b) ≤
        ConvexOptimization.lagrangian f₀ fc a b x lam nu := by
  classical
  let Q := (Fin mm → ℝ) × (Fin p → ℝ) × ℝ
  let perturb : EuclideanSpace ℝ (Fin n) → Q := fun x =>
    ((fun i => fc i x), (fun j => ⟪a j, x⟫ - b j), f₀ x)
  let C : Set Q := {q | ∃ x, (∀ i, fc i x ≤ q.1 i) ∧
    (∀ j, ⟪a j, x⟫ - b j = q.2.1 j) ∧ f₀ x ≤ q.2.2}
  have hperturb (x : EuclideanSpace ℝ (Fin n)) : perturb x ∈ C := by
    exact ⟨x, fun _ => le_rfl, fun _ => rfl, le_rfl⟩
  have hC : Convex ℝ C := by
    rw [convex_iff_add_mem]
    intro q₁ hq₁ q₂ hq₂ α β hα hβ hαβ
    obtain ⟨x₁, hx₁i, hx₁e, hx₁o⟩ := hq₁
    obtain ⟨x₂, hx₂i, hx₂e, hx₂o⟩ := hq₂
    refine ⟨α • x₁ + β • x₂, ?_, ?_, ?_⟩
    · intro i
      calc
        fc i (α • x₁ + β • x₂) ≤ α • fc i x₁ + β • fc i x₂ :=
          (hfc i).2 (by simp) (by simp) hα hβ hαβ
        _ ≤ α • q₁.1 i + β • q₂.1 i := by
          exact add_le_add (mul_le_mul_of_nonneg_left (hx₁i i) hα)
            (mul_le_mul_of_nonneg_left (hx₂i i) hβ)
        _ = (α • q₁ + β • q₂).1 i := by
          change α * q₁.1 i + β * q₂.1 i = α * q₁.1 i + β * q₂.1 i
          rfl
    · intro j
      calc
        ⟪a j, α • x₁ + β • x₂⟫ - b j =
            α * (⟪a j, x₁⟫ - b j) + β * (⟪a j, x₂⟫ - b j) := by
              rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
              linear_combination (b j) * hαβ
        _ = α * q₁.2.1 j + β * q₂.2.1 j := by rw [hx₁e j, hx₂e j]
        _ = (α • q₁ + β • q₂).2.1 j := by
          change α * q₁.2.1 j + β * q₂.2.1 j =
            α * q₁.2.1 j + β * q₂.2.1 j
          rfl
    · calc
        f₀ (α • x₁ + β • x₂) ≤ α • f₀ x₁ + β • f₀ x₂ :=
          hf₀.2 (by simp) (by simp) hα hβ hαβ
        _ ≤ α • q₁.2.2 + β • q₂.2.2 := by
          exact add_le_add (mul_le_mul_of_nonneg_left hx₁o hα)
            (mul_le_mul_of_nonneg_left hx₂o hβ)
        _ = (α • q₁ + β • q₂).2.2 := by
          change α * q₁.2.2 + β * q₂.2.2 = α * q₁.2.2 + β * q₂.2.2
          rfl
  have hsurj := slaterEqualityCoordinates_surjective a ha
  have hspan : affineSpan ℝ C = ⊤ := by
    let S := affineSpan ℝ C
    have hbase : perturb xs ∈ S := mem_affineSpan ℝ (hperturb xs)
    have hu (u : Fin mm → ℝ) : (u, (0, 0)) ∈ S.direction := by
      let r : Fin mm → ℝ := fun i => max 0 (-u i)
      let q₁ : Q := ((fun i => fc i xs + r i), (0, f₀ xs))
      let q₂ : Q := (u, (0, 0)) + q₁
      have hq₁ : q₁ ∈ C := by
        refine ⟨xs, ?_, ?_, ?_⟩
        · intro i
          dsimp [q₁, r]
          linarith [le_max_left 0 (-u i)]
        · intro j
          dsimp [q₁]
          rw [hxs_eq j]
          simp
        · exact le_rfl
      have hq₂ : q₂ ∈ C := by
        refine ⟨xs, ?_, ?_, ?_⟩
        · intro i
          change fc i xs ≤ u i + (fc i xs + max 0 (-u i))
          linarith [le_max_right 0 (-u i)]
        · intro j
          change ⟪a j, xs⟫ - b j = 0 + 0
          rw [hxs_eq j]
          simp
        · change f₀ xs ≤ 0 + f₀ xs
          simp
      have hd := AffineSubspace.vsub_mem_direction
        (mem_affineSpan ℝ hq₂) (mem_affineSpan ℝ hq₁)
      simpa [q₂] using hd
    have ht (t : ℝ) : ((0 : Fin mm → ℝ), (0, t)) ∈ S.direction := by
      let r : ℝ := max 0 (-t)
      let q₁ : Q := ((fun i => fc i xs), (0, f₀ xs + r))
      let q₂ : Q := ((0 : Fin mm → ℝ), (0, t)) + q₁
      have hq₁ : q₁ ∈ C := by
        refine ⟨xs, fun _ => le_rfl, ?_, ?_⟩
        · intro j
          dsimp [q₁]
          rw [hxs_eq j]
          simp
        · dsimp [q₁, r]
          linarith [le_max_left 0 (-t)]
      have hq₂ : q₂ ∈ C := by
        refine ⟨xs, ?_, ?_, ?_⟩
        · intro i
          change fc i xs ≤ 0 + fc i xs
          simp
        · intro j
          change ⟪a j, xs⟫ - b j = 0 + 0
          rw [hxs_eq j]
          simp
        · change f₀ xs ≤ t + (f₀ xs + max 0 (-t))
          linarith [le_max_right 0 (-t)]
      have hd := AffineSubspace.vsub_mem_direction
        (mem_affineSpan ℝ hq₂) (mem_affineSpan ℝ hq₁)
      simpa [q₂] using hd
    have hv (v : Fin p → ℝ) : ((0 : Fin mm → ℝ), (v, 0)) ∈ S.direction := by
      obtain ⟨y, hy⟩ := hsurj v
      let x := xs + y
      have hxres (j : Fin p) : ⟪a j, x⟫ - b j = v j := by
        dsimp [x]
        rw [inner_add_right, hxs_eq j, ← congrFun hy j]
        ring
      have hd := AffineSubspace.vsub_mem_direction
        (mem_affineSpan ℝ (hperturb x)) (mem_affineSpan ℝ (hperturb xs))
      have hd' : ((fun i => fc i x - fc i xs),
          (v, f₀ x - f₀ xs)) ∈ S.direction := by
        convert hd using 1
        ext i
        · rfl
        · dsimp [perturb]
          rw [hxres i, hxs_eq i]
          simp
        · rfl
      have hdu := hu (fun i => fc i x - fc i xs)
      have hdt := ht (f₀ x - f₀ xs)
      have hclean := S.direction.sub_mem (S.direction.sub_mem hd' hdu) hdt
      simpa using hclean
    have hdir : S.direction = ⊤ := by
      apply top_unique
      intro d _
      rcases d with ⟨u, v, t⟩
      have hadd := S.direction.add_mem (S.direction.add_mem (hu u) (hv v)) (ht t)
      simpa using hadd
    exact (AffineSubspace.direction_eq_top_iff_of_nonempty
      (s := S) ⟨perturb xs, hbase⟩).mp hdir
  have hCint : (interior C).Nonempty :=
    hC.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  let pstar : ℝ := sInf (f₀ '' ConvexOptimization.feasibleSet fc a b)
  let z : Q := ((0 : Fin mm → ℝ), (0, pstar))
  have hznot : z ∉ interior C := by
    intro hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    let z' : Q := ((0 : Fin mm → ℝ), (0, pstar - ε / 2))
    have habs : |pstar - ε / 2 - pstar| = ε / 2 := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have hz'dist : dist z' z < ε := by
      change max (dist (0 : Fin mm → ℝ) 0)
        (max (dist (0 : Fin p → ℝ) 0) (dist (pstar - ε / 2) pstar)) < ε
      rw [dist_self, dist_self, Real.dist_eq, habs]
      have hhalf : 0 ≤ ε / 2 := by linarith
      rw [max_eq_right hhalf, max_eq_right hhalf]
      linarith
    have hz'int := hball (Metric.mem_ball.mpr hz'dist)
    obtain ⟨x, hxi, hxe, hxo⟩ := interior_subset hz'int
    have hxfeas : x ∈ ConvexOptimization.feasibleSet fc a b := by
      refine ⟨?_, ?_⟩
      · intro i
        simpa [z'] using hxi i
      · intro j
        have := hxe j
        dsimp [z'] at this
        linarith
    have hp_le : pstar ≤ f₀ x := by
      exact csInf_le hbdd ⟨x, hxfeas, rfl⟩
    dsimp [z'] at hxo
    linarith
  obtain ⟨φ, hφne, hφ⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hC hznot hCint
  let g := -φ
  have hgne : g ≠ 0 := by
    intro hg
    apply hφne
    simpa [g] using hg
  have hsupport (q : Q) (hq : q ∈ C) : g z ≤ g q := by
    simpa [g] using neg_le_neg (hφ q hq)
  let eLam (i : Fin mm) : Q := (Pi.single i 1, (0, 0))
  let eNu (j : Fin p) : Q := ((0 : Fin mm → ℝ), (Pi.single j 1, 0))
  let eMu : Q := ((0 : Fin mm → ℝ), (0, 1))
  let lam₀ : Fin mm → ℝ := fun i => g (eLam i)
  let nu₀ : Fin p → ℝ := fun j => g (eNu j)
  let μ : ℝ := g eMu
  have hLamPart (u : Fin mm → ℝ) :
      g (u, (0, 0)) = ∑ i, u i * lam₀ i := by
    have hvec : (u, (0, 0)) = ∑ i, u i • eLam i := by
      apply Prod.ext
      · rw [Prod.fst_sum]
        exact pi_eq_sum_univ' u
      · rw [Prod.snd_sum]
        apply Prod.ext
        · rw [Prod.fst_sum]
          change (0 : Fin p → ℝ) = ∑ i, u i • (0 : Fin p → ℝ)
          simp
        · rw [Prod.snd_sum]
          change (0 : ℝ) = ∑ i, u i * 0
          simp
    rw [hvec, map_sum]
    simp [lam₀, mul_comm]
  have hNuPart (v : Fin p → ℝ) :
      g ((0 : Fin mm → ℝ), (v, 0)) = ∑ j, v j * nu₀ j := by
    have hvec : ((0 : Fin mm → ℝ), (v, 0)) = ∑ j, v j • eNu j := by
      apply Prod.ext
      · rw [Prod.fst_sum]
        change (0 : Fin mm → ℝ) = ∑ j, v j • (0 : Fin mm → ℝ)
        simp
      · rw [Prod.snd_sum]
        apply Prod.ext
        · rw [Prod.fst_sum]
          exact pi_eq_sum_univ' v
        · rw [Prod.snd_sum]
          change (0 : ℝ) = ∑ j, v j * 0
          simp
    rw [hvec, map_sum]
    simp [nu₀, mul_comm]
  have hMuPart (t : ℝ) : g ((0 : Fin mm → ℝ), (0, t)) = t * μ := by
    have hvec : ((0 : Fin mm → ℝ), (0, t)) = t • eMu := by
      dsimp [eMu]
      apply Prod.ext
      · change (0 : Fin mm → ℝ) = t • (0 : Fin mm → ℝ)
        simp
      · apply Prod.ext
        · change (0 : Fin p → ℝ) = t • (0 : Fin p → ℝ)
          simp
        · change t = t * 1
          ring
    rw [hvec, map_smul]
    simp [μ]
  have hdecomp (u : Fin mm → ℝ) (v : Fin p → ℝ) (t : ℝ) :
      g (u, (v, t)) =
        (∑ i, u i * lam₀ i) + (∑ j, v j * nu₀ j) + t * μ := by
    rw [show (u, (v, t)) =
      (u, (0, 0)) + ((0 : Fin mm → ℝ), (v, 0)) +
        ((0 : Fin mm → ℝ), (0, t)) by ext <;> simp]
    rw [map_add, map_add, hLamPart, hNuPart, hMuPart]
  let qb := perturb xs
  have hqbC : qb ∈ C := hperturb xs
  have hqbSupport : g z ≤ g qb := hsupport qb hqbC
  have hshiftLam (i : Fin mm) (r : ℝ) (hr : 0 ≤ r) : qb + r • eLam i ∈ C := by
    refine ⟨xs, ?_, ?_, ?_⟩
    · intro k
      by_cases hki : k = i
      · subst k
        change fc i xs ≤ fc i xs + r * (Pi.single i (1 : ℝ) : Fin mm → ℝ) i
        simp [hr]
      · change fc k xs ≤ fc k xs + r * (Pi.single i (1 : ℝ) : Fin mm → ℝ) k
        simp [Pi.single_apply, hki]
    · intro j
      change ⟪a j, xs⟫ - b j = (⟪a j, xs⟫ - b j) + r * 0
      ring
    · change f₀ xs ≤ f₀ xs + r * 0
      simp
  have hshiftMu (r : ℝ) (hr : 0 ≤ r) : qb + r • eMu ∈ C := by
    refine ⟨xs, ?_, ?_, ?_⟩
    · intro i
      change fc i xs ≤ fc i xs + r * 0
      simp
    · intro j
      change ⟪a j, xs⟫ - b j = (⟪a j, xs⟫ - b j) + r * 0
      ring
    · change f₀ xs ≤ f₀ xs + r * 1
      linarith
  have hlam₀ (i : Fin mm) : 0 ≤ lam₀ i := by
    by_contra h
    have hneg : lam₀ i < 0 := lt_of_not_ge h
    let r := (g qb - g z + 1) / (-lam₀ i)
    have hr : 0 < r := by
      dsimp [r]
      exact div_pos (by linarith) (neg_pos.mpr hneg)
    have hs := hsupport (qb + r • eLam i) (hshiftLam i r hr.le)
    have hgr : g (qb + r • eLam i) = g qb + r * lam₀ i := by
      simp [map_add, map_smul, lam₀]
    rw [hgr] at hs
    have hcalc : r * lam₀ i = -(g qb - g z + 1) := by
      dsimp [r]
      field_simp [hneg.ne]
    rw [hcalc] at hs
    linarith
  have hμnonneg : 0 ≤ μ := by
    by_contra h
    have hneg : μ < 0 := lt_of_not_ge h
    let r := (g qb - g z + 1) / (-μ)
    have hr : 0 < r := by
      dsimp [r]
      exact div_pos (by linarith) (neg_pos.mpr hneg)
    have hs := hsupport (qb + r • eMu) (hshiftMu r hr.le)
    have hgr : g (qb + r • eMu) = g qb + r * μ := by
      simp [map_add, map_smul, μ]
    rw [hgr] at hs
    have hcalc : r * μ = -(g qb - g z + 1) := by
      dsimp [r]
      field_simp [hneg.ne]
    rw [hcalc] at hs
    linarith
  have hμpos : 0 < μ := by
    refine lt_of_le_of_ne hμnonneg ?_
    intro hzero
    have hμzero : μ = 0 := hzero.symm
    have hgz := hdecomp (0 : Fin mm → ℝ) (0 : Fin p → ℝ) pstar
    have hgqb := hdecomp (fun i => fc i xs) (fun j => ⟪a j, xs⟫ - b j) (f₀ xs)
    have hsumge : 0 ≤ ∑ i, fc i xs * lam₀ i := by
      rw [hgz, hgqb] at hqbSupport
      simpa [z, qb, perturb, hxs_eq, hμzero] using hqbSupport
    have htermnonpos : ∀ i ∈ Finset.univ, fc i xs * lam₀ i ≤ 0 := by
      intro i _
      exact mul_nonpos_of_nonpos_of_nonneg (hxs_ineq i).le (hlam₀ i)
    have hsumnonpos : (∑ i, fc i xs * lam₀ i) ≤ 0 :=
      Finset.sum_nonpos htermnonpos
    have hsumeq : (∑ i, fc i xs * lam₀ i) = 0 :=
      le_antisymm hsumnonpos hsumge
    have hlamzero (i : Fin mm) : lam₀ i = 0 := by
      have hi := (Finset.sum_eq_zero_iff_of_nonpos htermnonpos).mp hsumeq i
        (Finset.mem_univ i)
      exact (mul_eq_zero.mp hi).resolve_left (ne_of_lt (hxs_ineq i))
    have hvineq (v : Fin p → ℝ) : 0 ≤ ∑ j, v j * nu₀ j := by
      obtain ⟨x, hx⟩ := hsurj (fun j => b j + v j)
      have hxres (j : Fin p) : ⟪a j, x⟫ - b j = v j := by
        have hj := congrFun hx j
        linarith
      have hs := hsupport (perturb x) (hperturb x)
      have hgqx := hdecomp (fun i => fc i x) (fun j => ⟪a j, x⟫ - b j) (f₀ x)
      rw [hgz, hgqx] at hs
      simpa [z, perturb, hxres, hμzero, hlamzero] using hs
    have hnuzero (j : Fin p) : nu₀ j = 0 := by
      have hj := hvineq (Pi.single j (-nu₀ j))
      simp [Pi.single_apply] at hj
      nlinarith [sq_nonneg (nu₀ j)]
    apply hgne
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨u, v, t⟩
    rw [hdecomp u v t]
    simp [hlamzero, hnuzero, hμzero]
  let lam : Fin mm → ℝ := fun i => lam₀ i / μ
  let nu : Fin p → ℝ := fun j => nu₀ j / μ
  refine ⟨lam, nu, ?_, ?_⟩
  · intro i
    exact div_nonneg (hlam₀ i) hμpos.le
  · intro x
    have hs := hsupport (perturb x) (hperturb x)
    have hgz := hdecomp (0 : Fin mm → ℝ) (0 : Fin p → ℝ) pstar
    have hgqx := hdecomp (fun i => fc i x) (fun j => ⟪a j, x⟫ - b j) (f₀ x)
    rw [hgz, hgqx] at hs
    have hraw : pstar * μ ≤
        (∑ i, fc i x * lam₀ i) + (∑ j, (⟪a j, x⟫ - b j) * nu₀ j) + f₀ x * μ := by
      simpa [z, perturb, mul_comm, mul_left_comm, mul_assoc] using hs
    have hlamSum : (∑ i, fc i x * lam₀ i) / μ =
        ∑ i, (lam₀ i / μ) * fc i x := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hμpos.ne']
    have hnuSum : (∑ j, (⟪a j, x⟫ - b j) * nu₀ j) / μ =
        ∑ j, (nu₀ j / μ) * (⟪a j, x⟫ - b j) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      field_simp [hμpos.ne']
    change pstar ≤ ConvexOptimization.lagrangian f₀ fc a b x lam nu
    rw [show ConvexOptimization.lagrangian f₀ fc a b x lam nu =
        ((∑ i, fc i x * lam₀ i) +
          (∑ j, (⟪a j, x⟫ - b j) * nu₀ j) + f₀ x * μ) / μ by
      simp only [ConvexOptimization.lagrangian, lam, nu]
      rw [← hlamSum, ← hnuSum]
      field_simp [hμpos.ne']
      ring]
    exact (le_div_iff₀ hμpos).2 hraw
