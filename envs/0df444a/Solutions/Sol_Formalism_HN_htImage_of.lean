-- Prove2me | solution 1 for Formalism.HN.htImage_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:14.724192+00:00
-- url     : https://prove2.me/submissions/88c713a0-51f0-4870-a22b-3208c637a230

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Theorems.Thm_Formalism_HN_place_part_orthogonal
import Theorems.Thm_Formalism_HN_orthogonal_complement_place_split
import Theorems.Thm_Formalism_HN_span_quotient_lattice_eq
import Theorems.Thm_Formalism_HN_htImage_map_mem
import Theorems.Thm_Formalism_HN_htImage_map_norm
import Theorems.Thm_Formalism_HN_htImage_realize_eq_zero
import Theorems.Thm_Formalism_HN_htImage_map_realize
import Theorems.Thm_Formalism_HN_htImage_mem_zl
import Theorems.Thm_Formalism_HN_htImage_zl_mono
import Theorems.Thm_Formalism_F_covolEqGram
import Theorems.Thm_Formalism_F_degQuot
import Theorems.Thm_P2M_Formalism_F_linearIndependent_coe_basis____9cab7951c4f4
import Theorems.Thm_P2M_Formalism_F_span_range_coe_basis__24da96608575


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (h1 : PlLat) (h2 : PlaceSplit) (h3 : GramBlock) : HtImage := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A hA
  classical
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  set A₀ := A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) with hA₀
  set I := A.map (φ.restrictScalars (𝓞 K)) with hI
  set Φ := htImageMap (htImageMat b X b' X' φ) with hΦ
  have hΦρ : ∀ x, Φ (ρ x) = ρ' (φ x) := htImage_map_realize b X b' X' hX φ
  have hinj' : ∀ w, ρ' w = 0 → w = 0 := fun w hw => htImage_realize_eq_zero b' X' hX' hw
  set L := zl ρ A with hL
  set N := zl ρ A₀ with hN
  set U := Submodule.span ℝ (N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) with hU
  have hNL : N ≤ L := htImage_zl_mono ρ inf_le_left
  have hUker : U ≤ LinearMap.ker Φ := by
    refine Submodule.span_le.2 fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := (htImage_mem_zl ρ A₀ y).1 hy
    have hφ : φ x = 0 := by simpa [A₀] using (Submodule.mem_inf.1 hx).2
    show Φ (ρ x) = 0
    rw [hΦρ, hφ, map_zero]
  have hsat : IsSat ρ A A₀ := by
    refine ⟨inf_le_left, hNL, fun y hyL hyU => ?_⟩
    obtain ⟨x, hx, rfl⟩ := (htImage_mem_zl ρ A y).1 hyL
    have h0 : Φ (ρ x) = 0 := hUker hyU
    rw [hΦρ] at h0
    have hφ : φ x = 0 := hinj' _ h0
    exact (htImage_mem_zl ρ A₀ _).2 ⟨x, Submodule.mem_inf.2 ⟨hx, by simpa using hφ⟩, rfl⟩
  refine ⟨hsat, ?_⟩
  have hA₀fg : A₀.FG := Submodule.FG.of_le hA inf_le_left
  have hIfg : I.FG := hA.map _
  obtain ⟨hLatA, hrkA, -⟩ := h1 K V ι b X hX A hA
  obtain ⟨hLatA₀, hrkA₀, -⟩ := h1 K V ι b X hX A₀ hA₀fg
  obtain ⟨hLatI, hrkI, -⟩ := h1 K W κ b' X' hX' I hIfg
  haveI hLd : DiscreteTopology L := hLatA.2
  haveI hId : DiscreteTopology (zl ρ' I) := hLatI.2
  obtain ⟨hQd, hrkQ, -⟩ := Formalism.F.degQuot _ L N hLd hsat.2
  set Q := Formalism.F.quot L N with hQ
  haveI := hQd

  have hπU : ∀ y ∈ U, Uᗮ.starProjection y = 0 := by
    intro y hy
    rw [Submodule.starProjection_orthogonal_val, (Submodule.starProjection_eq_self_iff).2 hy,
      sub_self]
  have hπ : ∀ z, Φ (Uᗮ.starProjection z) = Φ z := by
    intro z
    rw [Submodule.starProjection_orthogonal_val, map_sub]
    have : Φ (U.starProjection z) = 0 := hUker (Submodule.starProjection_apply_mem U z)
    rw [this, sub_zero]
  have hmemQ : ∀ q, q ∈ Q ↔ ∃ x ∈ A, Uᗮ.starProjection (ρ x) = q := by
    intro q
    simp only [hQ, Formalism.F.quot, Submodule.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (htImage_mem_zl ρ A z).1 hz
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ρ x, (htImage_mem_zl ρ A _).2 ⟨x, hx, rfl⟩, rfl⟩
  have hmaps : ∀ q : Q, ((Φ.restrictScalars ℤ).comp Q.subtype) q ∈ zl ρ' I := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx, rfl⟩ := (hmemQ q).1 hq
    show Φ (Uᗮ.starProjection (ρ x)) ∈ zl ρ' I
    rw [hπ, hΦρ]
    exact (htImage_mem_zl ρ' I _).2 ⟨φ x, Submodule.mem_map_of_mem hx, rfl⟩
  set f := LinearMap.codRestrict (zl ρ' I) ((Φ.restrictScalars ℤ).comp Q.subtype) hmaps with hf
  have hfinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun ⟨q, hq⟩ h0 => ?_
    have h0' : Φ q = 0 := congrArg Subtype.val h0
    obtain ⟨x, hx, rfl⟩ := (hmemQ q).1 hq
    rw [hπ, hΦρ] at h0'
    have hφ : φ x = 0 := hinj' _ h0'
    apply Subtype.ext
    show Uᗮ.starProjection (ρ x) = 0
    exact hπU _ (Submodule.subset_span
      ((htImage_mem_zl ρ A₀ _).2 ⟨x, Submodule.mem_inf.2 ⟨hx, by simpa using hφ⟩, rfl⟩))
  have hfsurj : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨i, hi, rfl⟩ := (htImage_mem_zl ρ' I w).1 hw
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hi
    refine ⟨⟨Uᗮ.starProjection (ρ x), (hmemQ _).2 ⟨x, hx, rfl⟩⟩, Subtype.ext ?_⟩
    show Φ (Uᗮ.starProjection (ρ x)) = ρ' (φ x)
    rw [hπ, hΦρ]
  let e := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩

  have hrkQI : Formalism.F.rk Q = Formalism.F.rk (zl ρ' I) := LinearEquiv.finrank_eq e
  have hd : 0 < Module.finrank ℚ K := Module.finrank_pos
  set s := rkK I with hs_def
  have hs : rkK A = rkK A₀ + s := by
    have e1 : Formalism.F.rk L = Module.finrank ℚ K * rkK A := hrkA
    have e2 : Formalism.F.rk N = Module.finrank ℚ K * rkK A₀ := hrkA₀
    have e3 : Formalism.F.rk (zl ρ' I) = Module.finrank ℚ K * s := hrkI
    have : Module.finrank ℚ K * rkK A = Module.finrank ℚ K * (rkK A₀ + s) := by
      rw [mul_add, ← e1, ← e2, ← e3, ← hrkQI, hrkQ]
    exact Nat.eq_of_mul_eq_mul_left hd this

  obtain ⟨hsplitA, hdimA⟩ := h2 K V ι b X hX A hA
  obtain ⟨hsplitA₀, hdimA₀⟩ := h2 K V ι b X hX A₀ hA₀fg
  have horth : ∀ v w : InfinitePlace K, v ≠ w →
      ∀ x ∈ (placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))),
      ∀ y ∈ (placePart w : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))),
      inner ℝ x y = 0 :=
    fun v w h x hx y hy => place_part_orthogonal h x hx y hy
  have horth' : ∀ v w : InfinitePlace K, v ≠ w →
      ∀ x ∈ (placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2))),
      ∀ y ∈ (placePart w : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2))),
      inner ℝ x y = 0 :=
    fun v w h x hx y hy => place_part_orthogonal h x hx y hy
  have hS' : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
      ⨆ v, Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓
        placePart v := hsplitA
  have hT' : U = ⨆ v, U ⊓ placePart v := hsplitA₀
  have hTS : U ≤ Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) :=
    Submodule.span_mono hNL
  obtain ⟨hWsplit, hWdim⟩ := orthogonal_complement_place_split
    (E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) (fun v => placePart v) horth
    _ U hS' hT' hTS
  have hWspan := span_quotient_lattice_eq L N hNL
  have hfr : ∀ v, Module.finrank ℝ (Submodule.span ℝ (Q : Set _) ⊓ placePart v :
      Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = 2 * s := by
    intro v
    have a1 : Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ Uᗮ ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) +
        Module.finrank ℝ (U ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := hWdim v
    have a2 : Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = 2 * rkK A := hdimA v
    have a3 : Module.finrank ℝ (U ⊓ placePart v : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        2 * rkK A₀ := hdimA₀ v
    have a4 : Module.finrank ℝ (Submodule.span ℝ (Q : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
        Module.finrank ℝ (Submodule.span ℝ (L : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ Uᗮ ⊓ placePart v :
        Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
      rw [hWspan]
    omega

  let u := Module.finBasis ℤ Q
  let u' : Fin (Module.finrank ℤ Q) → EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) :=
    fun i => (u i : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))
  have hli : LinearIndependent ℝ u' := Formalism.F.linearIndependent_coe_basis''' Q u
  have hspan : Submodule.span ℝ (Set.range u') = Submodule.span ℝ (Q : Set _) := by
    rw [← Submodule.span_span_of_tower ℤ ℝ (Set.range u')]
    exact congrArg (fun M : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) =>
      Submodule.span ℝ (M : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))
      (Formalism.F.span_range_coe_basis' Q u)
  have hcovQ : Formalism.F.covol Q = Real.sqrt (Matrix.gram ℝ u').det :=
    Formalism.F.covolEqGram _ Q _ u
  have hcovI : Formalism.F.covol (zl ρ' I) = Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det := by
    rw [Formalism.F.covolEqGram _ (zl ρ' I) _ (u.map e)]
    congr 3

  have hG := (h3 (InfinitePlace K) _ _ (Fin (Module.finrank ℤ Q)) (fun v => placePart v)
    (fun v => placePart v) Φ (fun v => opNormAt b X b' X' v φ) (Submodule.span ℝ (Q : Set _)) u'
    horth horth' (fun v => norm_nonneg _)
    (fun v x hx => ⟨htImage_map_mem _ hx, htImage_map_norm _ hx⟩)
    (by rw [hWspan]; exact hWsplit) hli hspan).1
  simp only [hfr] at hG

  set C := ∏ v, opNormAt b X b' X' v φ ^ (2 * s) with hC
  have hC0 : 0 ≤ C := Finset.prod_nonneg fun v _ => pow_nonneg (norm_nonneg _) _
  have hC2 : (∏ v, opNormAt b X b' X' v φ ^ (2 * (2 * s))) = C ^ 2 := by
    rw [hC, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul]; ring_nf
  rw [hC2] at hG
  have hsq : Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det ≤
      C * Real.sqrt (Matrix.gram ℝ u').det := by
    calc Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det
        ≤ Real.sqrt (C ^ 2 * (Matrix.gram ℝ u').det) := Real.sqrt_le_sqrt hG
      _ = C * Real.sqrt (Matrix.gram ℝ u').det := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC0]
  have hsR : (rkK A : ℝ) - rkK A₀ = s := by rw [hs]; push_cast; ring
  have h2pow : (2 : ℝ) ^ ((nPl K : ℝ) * (s : ℝ)) = 2 ^ (nPl K * s) := by
    rw [← Nat.cast_mul, Real.rpow_natCast]
  unfold ht htQ
  rw [hsR, h2pow, hcovQ, ← hs_def, hcovI]
  have ha : 0 ≤ (2 : ℝ) ^ (nPl K * s) * |(NumberField.discr K : ℝ)| ^ (-(s : ℝ) / 2) := by
    positivity
  calc (2 : ℝ) ^ (nPl K * s) * |(NumberField.discr K : ℝ)| ^ (-(s : ℝ) / 2) *
        Real.sqrt (Matrix.gram ℝ (fun i => Φ (u' i))).det
      ≤ (2 : ℝ) ^ (nPl K * s) * |(NumberField.discr K : ℝ)| ^ (-(s : ℝ) / 2) *
        (C * Real.sqrt (Matrix.gram ℝ u').det) := mul_le_mul_of_nonneg_left hsq ha
    _ = C * ((2 : ℝ) ^ (nPl K * s) * |(NumberField.discr K : ℝ)| ^ (-(s : ℝ) / 2) *
        Real.sqrt (Matrix.gram ℝ u').det) := by ring
end Formalism.HN
