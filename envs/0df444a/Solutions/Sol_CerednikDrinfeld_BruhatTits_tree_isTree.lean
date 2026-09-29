-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.tree_isTree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c05e06e5-ef3b-52f3-b7a7-0cdea53ec4fc

import Mathlib
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_tree_isTree

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "VertRel tree tree_adj_iff"
namespace BruhatTits
p2m_export "CerednikDrinfeld.BruhatTits" "tree_adj_iff VertRel tree"
namespace TreeCC
p2m_open "CerednikDrinfeld.BruhatTits CerednikDrinfeld"

section Colen

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {M' : Type*} [AddCommGroup M'] [Module R M']

noncomputable def colen (N L : Submodule R M) : ℕ∞ :=
  Module.length R (↥L ⧸ N.comap L.subtype)

theorem colen_eq_zero_iff (N L : Submodule R M) : colen N L = 0 ↔ L ≤ N := by
  rw [colen, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Submodule.comap_subtype_eq_top]

theorem colen_self (L : Submodule R M) : colen L L = 0 := (colen_eq_zero_iff L L).mpr le_rfl

theorem colen_pos_iff (N L : Submodule R M) : 0 < colen N L ↔ ¬ L ≤ N := by
  rw [pos_iff_ne_zero, Ne, colen_eq_zero_iff]

theorem colen_eq_add {N' N L : Submodule R M} (h1 : N' ≤ N) (h2 : N ≤ L) :
    colen N' L = colen N L + colen N' N := by
  classical
  let A : Submodule R ↥L := N.comap L.subtype
  let B : Submodule R ↥L := N'.comap L.subtype
  have hBA : B ≤ A := Submodule.comap_mono h1
  let ι : ↥N →ₗ[R] ↥L := Submodule.inclusion h2
  have hι : N'.comap N.subtype ≤ B.comap ι := fun x hx => hx
  let f : (↥N ⧸ N'.comap N.subtype) →ₗ[R] (↥L ⧸ B) := Submodule.mapQ _ B ι hι
  let g : (↥L ⧸ B) →ₗ[R] (↥L ⧸ A) := Submodule.mapQ B A LinearMap.id hBA
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Submodule.Quotient.induction_on with | _ a => ?_
    induction y using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [f, Submodule.mapQ_apply] at hxy
    rw [Submodule.Quotient.eq] at hxy ⊢
    rw [← map_sub] at hxy
    exact hxy
  have hg : Function.Surjective g := by
    intro x
    induction x using Submodule.Quotient.induction_on with | _ a => ?_
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ l => ?_
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, Set.mem_range]
    constructor
    · intro hl
      refine ⟨Submodule.Quotient.mk ⟨(l : M), hl⟩, ?_⟩
      simp only [f, Submodule.mapQ_apply]
      congr 1
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | _ n => ?_
      simp only [f, Submodule.mapQ_apply] at hx
      rw [Submodule.Quotient.eq] at hx

      have h3 : ((ι n - l : ↥L) : M) ∈ N := h1 hx
      have h4 : ((ι n : ↥L) : M) ∈ N := n.2
      have : (l : M) = (ι n : ↥L) - (ι n - l : ↥L) := by simp
      show (l : M) ∈ N
      rw [this, Submodule.coe_sub]
      exact N.sub_mem h4 h3
  rw [colen, colen, colen, Module.length_eq_add_of_exact f g hf hg hex, add_comm]

theorem colen_map (f : M →ₗ[R] M') (hf : Function.Injective f) (N L : Submodule R M) :
    colen (N.map f) (L.map f) = colen N L := by
  unfold colen
  symm
  refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf L) ?_)
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (Submodule.coe_equivMapOfInjective_apply f hf L x).symm⟩
  · rintro ⟨n, hn, hny⟩
    obtain ⟨l, hl, hly⟩ := (Submodule.mem_map.mp y.2)
    have hnl : n = l := hf (hny.trans hly.symm)
    refine ⟨⟨l, hl⟩, ?_, ?_⟩
    · show (l : M) ∈ N
      rw [← hnl]; exact hn
    · apply Subtype.ext
      exact (Submodule.coe_equivMapOfInjective_apply f hf L ⟨l, hl⟩).trans hly

theorem colen_mono_left {N₁ N₂ L : Submodule R M} (h : N₁ ≤ N₂) (h2 : N₂ ≤ L) :
    colen N₂ L ≤ colen N₁ L := by
  rw [colen_eq_add h h2]
  exact le_self_add

theorem colen_lt_of_lt {N₁ N₂ L : Submodule R M} (h : N₁ < N₂) (h2 : N₂ ≤ L) (hfin : colen N₁ L ≠ ⊤) :
    colen N₂ L < colen N₁ L := by
  rw [colen_eq_add h.le h2] at hfin ⊢
  have hpos : 0 < colen N₁ N₂ := (colen_pos_iff _ _).mpr (not_le_of_gt h)
  have hne : colen N₂ L ≠ ⊤ := fun h' => hfin (by rw [h', top_add])
  have := (ENat.add_lt_add_iff_left hne).mpr hpos
  rwa [add_zero] at this

end Colen

section Lattices

open LT.LatticeTree Submodule

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

theorem isLattice_of_isFullLattice {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    Submodule.IsLattice K L := ⟨hL.1, hL.2⟩

theorem finrank_eq_two {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) : Module.finrank R ↥L = 2 := by
  haveI := isLattice_of_isFullLattice hL
  simpa using Submodule.IsLattice.finrank_of_pi K L

scoped instance free_of_isFullLattice' {L : Submodule R (Fin 2 → K)} [Submodule.IsLattice K L] : Module.Free R ↥L :=
  inferInstance

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem comap_subtype_pointwise_smul (r : R) (L : Submodule R (Fin 2 → K)) :
    (r • L).comap L.subtype = r • (⊤ : Submodule R ↥L) := by
  ext x
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  · rintro ⟨y, hyx⟩
    exact ⟨y, y.2, congrArg Subtype.val hyx⟩

theorem colen_smul_eq_two {ϖ : R} (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    colen (ϖ • L) L = 2 := by
  haveI := isLattice_of_isFullLattice hL
  let b := Module.finBasisOfFinrankEq R ↥L (finrank_eq_two hL)
  let e : ↥L ≃ₗ[R] (Fin 2 → R) := b.equivFun
  rw [colen, comap_subtype_pointwise_smul]
  have h1 : Module.length R (↥L ⧸ ϖ • (⊤ : Submodule R ↥L)) =
      Module.length R ((Fin 2 → R) ⧸ ϖ • (⊤ : Submodule R (Fin 2 → R))) :=
    LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e (by
      rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range]))
  rw [h1]
  have h2 : (ϖ • (⊤ : Submodule R (Fin 2 → R))) =
      Submodule.pi Set.univ (fun _ : Fin 2 => (Ideal.span {ϖ} : Submodule R R)) := by
    ext v
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, Submodule.mem_pi,
      Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨w, rfl⟩ i
      exact Ideal.mem_span_singleton'.mpr ⟨w i, by simp [mul_comm]⟩
    · intro h
      choose w hw using fun i => Ideal.mem_span_singleton'.mp (h i)
      exact ⟨w, funext fun i => by simp [← hw i, mul_comm]⟩
  rw [h2, LinearEquiv.length_eq (Submodule.quotientPi _), Module.length_pi_of_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h3 : Module.length R (R ⧸ (Ideal.span {ϖ} : Submodule R R)) = 1 := by
    rw [LinearEquiv.length_eq (Submodule.quotEquivOfEq _ _ hϖ.maximalIdeal_eq.symm)]
    have := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := R) 1
    rwa [pow_one] at this
  rw [h3]
  rfl

omit [IsDiscreteValuationRing R] in

theorem pointwise_smul_eq_latticeMap {r : R} (hr : r ≠ 0) (L : Submodule R (Fin 2 → K)) :
    r • L = latticeMap (scalarGL (unitOfNeZero (K := K) hr)) L := by
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists, mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by rw [unitOfNeZero_coe, algebraMap_smul]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, by rw [unitOfNeZero_coe, algebraMap_smul]⟩

omit [IsDiscreteValuationRing R] in
theorem isFullLattice_pointwise_smul {r : R} (hr : r ≠ 0) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    IsFullLattice (r • L) := by
  rw [pointwise_smul_eq_latticeMap hr]
  exact hL.map _

omit [IsDiscreteValuationRing R] in
theorem homothetic_pointwise_smul {r : R} (hr : r ≠ 0) (L : Submodule R (Fin 2 → K)) :
    Homothetic L (r • L) :=
  ⟨unitOfNeZero (K := K) hr, (pointwise_smul_eq_latticeMap hr L).symm⟩

end Lattices

section Lattices2

open LT.LatticeTree Submodule

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

theorem pointwise_smul_le_self (r : R) (L : Submodule R (Fin 2 → K)) : r • L ≤ L := by
  rintro _ ⟨y, hy, rfl⟩
  exact L.smul_mem r hy

theorem pointwise_smul_mono (r : R) {A B : Submodule R (Fin 2 → K)} (h : A ≤ B) : r • A ≤ r • B := by
  rintro _ ⟨y, hy, rfl⟩
  exact Submodule.smul_mem_pointwise_smul y r B (h hy)

theorem le_of_unit_mul_smul_le {u : Rˣ} {r : R} {A B : Submodule R (Fin 2 → K)} (h : ((u : R) * r) • A ≤ B) :
    r • A ≤ B := by
  rintro _ ⟨y, hy, rfl⟩
  have h1 : ((u : R) * r) • y ∈ B := h (Submodule.smul_mem_pointwise_smul y _ A hy)
  have h2 : r • y = ((u⁻¹ : Rˣ) : R) • (((u : R) * r) • y) := by
    rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
  show r • y ∈ B
  rw [h2]
  exact B.smul_mem _ h1

theorem pointwise_smul_le_ideal_smul (r : R) (L : Submodule R (Fin 2 → K)) :
    r • L ≤ (Ideal.span {r} : Ideal R) • L := by
  rintro _ ⟨y, hy, rfl⟩
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) hy

theorem ne_bot_of_isFullLattice {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) : L ≠ ⊥ := by
  rintro rfl
  have h := hL.2
  rw [Submodule.bot_coe, Submodule.span_singleton_eq_bot.mpr rfl] at h
  exact bot_ne_top h

theorem le_of_le_sup_smul {ϖ : R} (hϖ : Irreducible ϖ) {N L : Submodule R (Fin 2 → K)} (hL : L.FG)
    (h : L ≤ N ⊔ ϖ • L) : L ≤ N := by
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hL (I := Ideal.span {ϖ})
  · rw [← hϖ.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal_le_jacobson _
  · exact h.trans (sup_le_sup_left (pointwise_smul_le_ideal_smul ϖ L) _)

theorem smul_ne_self {ϖ : R} (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ϖ • L ≠ L := by
  intro h
  apply ne_bot_of_isFullLattice hL
  rw [eq_bot_iff]
  exact le_of_le_sup_smul hϖ hL.1 (by rw [bot_sup_eq, h])

theorem exists_smul_mem_of_isFullLattice {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) (v : Fin 2 → K) :
    ∃ s : R, s ≠ 0 ∧ s • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set (Fin 2 → K)) := hL.2 ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨t * s, mul_ne_zero ht hs, ?_⟩
    rw [smul_add, mul_smul, mul_comm, mul_smul]
    exact L.add_mem (L.smul_mem t hsx) (L.smul_mem s hty)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨a, d⟩, had⟩ := IsLocalization.surj (nonZeroDivisors R) c
    refine ⟨(d : R) * s, mul_ne_zero (nonZeroDivisors.ne_zero d.2) hs, ?_⟩
    rw [mul_smul, smul_comm s c x, ← algebraMap_smul K (d : R), smul_smul, mul_comm, had, algebraMap_smul]
    exact L.smul_mem a hsx

theorem exists_smul_le_of_fg_of_isFullLattice {ϖ : R} (hϖ : Irreducible ϖ)
    {M L : Submodule R (Fin 2 → K)} (hM : M.FG) (hL : IsFullLattice L) :
    ∃ n : ℕ, ϖ ^ n • M ≤ L := by
  classical
  obtain ⟨S, rfl⟩ := hM

  have key : ∃ s : R, s ≠ 0 ∧ ∀ x ∈ S, s • x ∈ L := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, fun x hx => absurd hx (Finset.notMem_empty x)⟩
    | insert a S haS ih =>
      obtain ⟨s, hs, hS⟩ := ih
      obtain ⟨t, ht, hta⟩ := exists_smul_mem_of_isFullLattice hL a
      refine ⟨s * t, mul_ne_zero hs ht, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rw [mul_smul]; exact L.smul_mem s hta
      · rw [mul_comm, mul_smul]; exact L.smul_mem t (hS x hx)
  obtain ⟨s, hs, hS⟩ := key
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  refine ⟨n, le_of_unit_mul_smul_le (u := u) ?_⟩
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact hS x hx

theorem exists_smul_le {ϖ : R} (hϖ : Irreducible ϖ) {M L : Submodule R (Fin 2 → K)}
    (hM : IsFullLattice M) (hL : IsFullLattice L) : ∃ n : ℕ, ϖ ^ n • M ≤ L :=
  exists_smul_le_of_fg_of_isFullLattice hϖ hM.1 hL

omit [IsDiscreteValuationRing R] in
theorem colen_pointwise_smul {r : R} (hr : r ≠ 0) (N L : Submodule R (Fin 2 → K)) :
    colen (r • N) (r • L) = colen N L := by
  have hinj : Function.Injective (DistribSMul.toLinearMap R (Fin 2 → K) r) := by
    intro x y hxy
    simp only [DistribSMul.toLinearMap_apply] at hxy
    rw [← algebraMap_smul K r x, ← algebraMap_smul K r y] at hxy
    exact smul_right_injective (Fin 2 → K)
      (fun h => hr (IsFractionRing.injective R K (by rw [h, map_zero]))) hxy
  have hmap : ∀ A : Submodule R (Fin 2 → K), A.map (DistribSMul.toLinearMap R (Fin 2 → K) r) = r • A := by
    intro A; ext x
    simp only [Submodule.mem_map, DistribSMul.toLinearMap_apply, Submodule.mem_smul_pointwise_iff_exists]
  rw [← hmap N, ← hmap L]
  exact colen_map _ hinj N L

theorem colen_pow_smul {ϖ : R} (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) (n : ℕ) :
    colen (ϖ ^ n • L) L = 2 * n := by
  induction n with
  | zero => rw [pow_zero, one_smul, colen_self]; simp
  | succ n ih =>
    have h1 : ϖ ^ (n + 1) • L ≤ ϖ ^ n • L := by
      rw [pow_succ, mul_smul]
      exact pointwise_smul_mono _ (pointwise_smul_le_self ϖ L)
    rw [colen_eq_add h1 (pointwise_smul_le_self _ L), ih, pow_succ, mul_smul, colen_pointwise_smul (pow_ne_zero n hϖ.ne_zero),
      colen_smul_eq_two hϖ hL]
    push_cast
    ring

theorem colen_ne_top {ϖ : R} (hϖ : Irreducible ϖ) {N L : Submodule R (Fin 2 → K)}
    (hN : IsFullLattice N) (hL : IsFullLattice L) (hNL : N ≤ L) : colen N L ≠ ⊤ := by
  obtain ⟨n, hn⟩ := exists_smul_le hϖ hL hN
  have h := colen_mono_left hn hNL
  rw [colen_pow_smul hϖ hL] at h
  intro htop
  rw [htop, top_le_iff] at h
  exact (ENat.coe_ne_top (2 * n)) (by exact_mod_cast h)

end Lattices2

section Connectivity

open LT.LatticeTree Submodule

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_smul_eq_of_le_smul {ϖ : R} (hϖ : Irreducible ϖ) {N L : Submodule R (Fin 2 → K)}
    (hN : IsFullLattice N) (hNL : N ≤ ϖ • L) :
    ∃ N₁ : Submodule R (Fin 2 → K), IsFullLattice N₁ ∧ Homothetic N N₁ ∧ ϖ • N₁ = N ∧ N₁ ≤ L := by
  let u : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero
  refine ⟨latticeMap (scalarGL u⁻¹) N, hN.map _, ⟨u⁻¹, rfl⟩, ?_, ?_⟩
  · rw [pointwise_smul_eq_latticeMap hϖ.ne_zero, ← latticeMap_mul, ← scalarGL_mul, mul_inv_cancel, scalarGL_one,
      latticeMap_one]
  · intro v hv
    rw [mem_latticeMap_scalarGL] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨l, hl, hlw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hNL hw)
    rw [← hlw, ← algebraMap_smul K ϖ l, smul_smul, Units.val_inv_eq_inv_val, unitOfNeZero_coe,
      inv_mul_cancel₀ (fun h => hϖ.ne_zero (IsFractionRing.injective R K (by rw [h, map_zero]))), one_smul]
    exact hl

theorem isFullLattice_sup {A B : Submodule R (Fin 2 → K)} (hA : IsFullLattice A) (hB : IsFullLattice B) :
    IsFullLattice (A ⊔ B) :=
  ⟨Submodule.FG.sup hA.1 hB.1, eq_top_iff.mpr (hA.2 ▸ Submodule.span_mono (show (A : Set (Fin 2 → K)) ⊆ ↑(A ⊔ B) from
    fun _ hx => Submodule.mem_sup_left hx))⟩

theorem enat_le_of_lt_succ {a : ℕ∞} {k : ℕ} (h : a < (k + 1 : ℕ)) : a ≤ k := by
  rw [Nat.cast_succ] at h
  exact (ENat.lt_add_one_iff (ENat.coe_ne_top k)).mp h

theorem reachable_of_le {ϖ : R} (hϖ : Irreducible ϖ) :
    ∀ (k : ℕ) {N L : Submodule R (Fin 2 → K)} (hN : IsFullLattice N) (hL : IsFullLattice L),
      N ≤ L → colen N L ≤ k → (tree R K).Reachable (Vertex.mk R K L hL) (Vertex.mk R K N hN) := by
  intro k
  induction k with
  | zero =>
    intro N L hN hL hNL hk
    have hLN : L ≤ N := (colen_eq_zero_iff N L).mp (nonpos_iff_eq_zero.mp (by exact_mod_cast hk))
    obtain rfl : N = L := le_antisymm hNL hLN
    rfl
  | succ k ih =>
    intro N L hN hL hNL hk
    by_cases h0 : L ≤ N
    · obtain rfl : N = L := le_antisymm hNL h0
      rfl
    have hfin := colen_ne_top hϖ hN hL hNL
    by_cases h1 : N ≤ ϖ • L
    ·
      obtain ⟨N₁, hN₁, hhom, hϖN₁, hN₁L⟩ := exists_smul_eq_of_le_smul hϖ hN h1
      have hle : N ≤ N₁ := by rw [← hϖN₁]; exact pointwise_smul_le_self ϖ N₁
      have hlt : N < N₁ := lt_of_le_of_ne hle (fun h => smul_ne_self hϖ hN₁ (hϖN₁.trans h))
      have hk' : colen N₁ L ≤ k := enat_le_of_lt_succ (lt_of_lt_of_le (colen_lt_of_lt hlt hN₁L hfin) hk)
      rw [show Vertex.mk R K N hN = Vertex.mk R K N₁ hN₁ from Vertex.mk_eq_mk_iff.mpr hhom]
      exact ih hN₁ hL hN₁L hk'
    ·
      have hϖL : IsFullLattice (ϖ • L) := isFullLattice_pointwise_smul hϖ.ne_zero hL
      have hL'full : IsFullLattice (N ⊔ ϖ • L) := isFullLattice_sup hN hϖL
      have hL'L : N ⊔ ϖ • L ≤ L := sup_le hNL (pointwise_smul_le_self ϖ L)
      have hNL' : N ≤ N ⊔ ϖ • L := le_sup_left
      have hne1 : N ⊔ ϖ • L ≠ L := fun h => h0 (le_of_le_sup_smul hϖ hL.1 h.symm.le)
      have hne2 : ϖ • L ≠ N ⊔ ϖ • L := fun h => h1 (h.symm ▸ le_sup_left)
      have hadj : AdjacentLattice L (N ⊔ ϖ • L) :=
        ⟨ϖ, hϖ, by rw [← pointwise_smul_eq_latticeMap]; exact lt_of_le_of_ne le_sup_right hne2,
          lt_of_le_of_ne hL'L hne1⟩
      have hreach1 : (tree R K).Reachable (Vertex.mk R K L hL) (Vertex.mk R K (N ⊔ ϖ • L) hL'full) := by
        by_cases heq : Vertex.mk R K L hL = Vertex.mk R K (N ⊔ ϖ • L) hL'full
        · rw [heq]
        · exact SimpleGraph.Adj.reachable ((tree_adj_iff _ _).mpr ⟨heq, Or.inl ⟨L, _, hL, hL'full, rfl, rfl, hadj⟩⟩)
      have hsplit := colen_eq_add hNL' hL'L
      have hpos : 0 < colen (N ⊔ ϖ • L) L := (colen_pos_iff _ _).mpr (fun h => hne1 (le_antisymm hL'L h))
      have hne : colen N (N ⊔ ϖ • L) ≠ ⊤ := fun h => hfin (by rw [hsplit, h, add_top])
      have hlt : colen N (N ⊔ ϖ • L) < colen N L := by
        rw [hsplit]
        have := (ENat.add_lt_add_iff_left hne).mpr hpos
        rwa [add_zero, add_comm] at this
      exact hreach1.trans (ih hN hL'full hNL' (enat_le_of_lt_succ (lt_of_lt_of_le hlt hk)))

theorem tree_preconnected : (tree R K).Preconnected := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  intro x y
  induction x using Quotient.inductionOn with | h L => ?_
  induction y using Quotient.inductionOn with | h M => ?_
  obtain ⟨n, hn⟩ := exists_smul_le hϖ M.2 L.2
  have hMn : IsFullLattice (ϖ ^ n • M.1) := isFullLattice_pointwise_smul (pow_ne_zero n hϖ.ne_zero) M.2
  have h1 : (tree R K).Reachable (Vertex.mk R K L.1 L.2) (Vertex.mk R K (ϖ ^ n • M.1) hMn) := by
    refine reachable_of_le hϖ (colen (ϖ ^ n • M.1) L.1).toNat hMn L.2 hn ?_
    rw [ENat.coe_toNat (colen_ne_top hϖ hMn L.2 hn)]
  have h2 : Vertex.mk R K (ϖ ^ n • M.1) hMn = Vertex.mk R K M.1 M.2 :=
    Vertex.mk_eq_mk_iff.mpr (homothetic_pointwise_smul (pow_ne_zero n hϖ.ne_zero) M.1).symm
  rw [h2] at h1
  exact h1

theorem tree_connected : (tree R K).Connected :=
  @SimpleGraph.Connected.mk _ _ tree_preconnected ⟨stdVertex R K⟩

end Connectivity

section Colouring

open LT.LatticeTree Submodule

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

theorem unit_smul_eq (u : Rˣ) (L : Submodule R (Fin 2 → K)) : (u : R) • L = L := by
  refine le_antisymm (pointwise_smul_le_self _ L) ?_
  intro x hx
  have : x = (u : R) • (((u⁻¹ : Rˣ) : R) • x) := by
    rw [smul_smul, Units.mul_inv, one_smul]
  rw [this]
  exact Submodule.smul_mem_pointwise_smul _ _ L (L.smul_mem _ hx)

theorem unit_mul_smul_eq (u : Rˣ) (r : R) (L : Submodule R (Fin 2 → K)) : ((u : R) * r) • L = r • L := by
  rw [mul_comm, mul_smul, unit_smul_eq]

theorem colen_pow_succ_smul {ϖ : R} (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (m : ℕ) (h : ϖ ^ m • L ≤ M) : colen (ϖ ^ (m + 1) • L) M = colen (ϖ ^ m • L) M + 2 := by
  have hfull : IsFullLattice (ϖ ^ m • L) := isFullLattice_pointwise_smul (pow_ne_zero m hϖ.ne_zero) hL
  have h1 : ϖ ^ (m + 1) • L = ϖ • (ϖ ^ m • L) := by rw [pow_succ', mul_smul]
  rw [h1, colen_eq_add (pointwise_smul_le_self ϖ _) h, colen_smul_eq_two hϖ hfull]

noncomputable def parityAt (ϖ : R) (L M : Submodule R (Fin 2 → K)) (n : ℕ) : ZMod 2 :=
  ((colen (ϖ ^ n • L) M).toNat : ZMod 2)

theorem parityAt_add {ϖ : R} (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (hM : IsFullLattice M) (m : ℕ) (h : ϖ ^ m • L ≤ M) (d : ℕ) : parityAt ϖ L M (m + d) = parityAt ϖ L M m := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hle : ϖ ^ (m + d) • L ≤ M := by
      rw [pow_add, mul_comm, mul_smul]
      exact (pointwise_smul_le_self _ _).trans h
    have hfin : colen (ϖ ^ (m + d) • L) M ≠ ⊤ :=
      colen_ne_top hϖ (isFullLattice_pointwise_smul (pow_ne_zero _ hϖ.ne_zero) hL) hM hle
    rw [← ih, parityAt, parityAt, ← add_assoc, colen_pow_succ_smul hϖ hL (m + d) hle,
      ENat.toNat_add hfin (by decide), Nat.cast_add]
    simp only [ENat.toNat_ofNat, Nat.cast_ofNat]
    rw [show (2 : ZMod 2) = 0 from rfl, add_zero]

theorem parityAt_eq_of_le {ϖ : R} (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (hM : IsFullLattice M) {m n : ℕ} (hm : ϖ ^ m • L ≤ M) (hn : ϖ ^ n • L ≤ M) :
    parityAt ϖ L M m = parityAt ϖ L M n := by
  rcases le_total m n with hmn | hnm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact (parityAt_add hϖ hL hM m hm d).symm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact parityAt_add hϖ hL hM n hn d

open Classical in

noncomputable def parity {ϖ : R} (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) : ZMod 2 :=
  parityAt ϖ L (stdLattice R K) (Nat.find (exists_smul_le hϖ hL (isFullLattice_stdLattice (R := R) (K := K))))

theorem parity_eq {ϖ : R} (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    {n : ℕ} (hn : ϖ ^ n • L ≤ stdLattice R K) : parity hϖ L hL = parityAt ϖ L (stdLattice R K) n := by
  classical
  unfold parity
  exact parityAt_eq_of_le hϖ hL isFullLattice_stdLattice
    (Nat.find_spec (exists_smul_le hϖ hL (isFullLattice_stdLattice (R := R) (K := K)))) hn

theorem exists_pow_smul_eq_of_homothetic {ϖ : R} (hϖ : Irreducible ϖ) {L L' : Submodule R (Fin 2 → K)}
    (h : Homothetic L L') : ∃ i j : ℕ, ϖ ^ j • L' = ϖ ^ i • L := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj (nonZeroDivisors R) (c : K)

  have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at has
    rcases has with h | h
    · exact c.ne_zero h
    · exact hs (IsFractionRing.injective R K (by rw [h, map_zero]))
  obtain ⟨i, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨j, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  refine ⟨i, j, ?_⟩
  have key : (s : R) • latticeMap (scalarGL c) L = a • L := by
    rw [pointwise_smul_eq_latticeMap hs, pointwise_smul_eq_latticeMap ha, ← latticeMap_mul, ← scalarGL_mul]
    congr 2
    ext
    rw [Units.val_mul, unitOfNeZero_coe, unitOfNeZero_coe, mul_comm, has]
  rw [hu, hu', unit_mul_smul_eq, unit_mul_smul_eq] at key
  exact key

theorem parity_eq_of_homothetic {ϖ : R} (hϖ : Irreducible ϖ) {L L' : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (hL' : IsFullLattice L') (h : Homothetic L L') : parity hϖ L hL = parity hϖ L' hL' := by
  obtain ⟨i, j, hij⟩ := exists_pow_smul_eq_of_homothetic hϖ h
  obtain ⟨n, hn⟩ := exists_smul_le hϖ hL (isFullLattice_stdLattice (R := R) (K := K))
  have hni : ϖ ^ (n + i) • L ≤ stdLattice R K := by
    rw [pow_add, mul_comm, mul_smul]; exact (pointwise_smul_le_self _ _).trans hn
  have heq : ϖ ^ (n + j) • L' = ϖ ^ (n + i) • L := by
    rw [pow_add, pow_add, mul_smul, mul_smul, hij]
  have hnj : ϖ ^ (n + j) • L' ≤ stdLattice R K := heq ▸ hni
  rw [parity_eq hϖ hL hni, parity_eq hϖ hL' hnj, parityAt, parityAt, heq]

theorem enat_eq_one_of_add_eq_two {a b : ℕ∞} (h : a + b = 2) (ha : a ≠ 0) (hb : b ≠ 0) : a = 1 := by
  have ha' : a ≠ ⊤ := by rintro rfl; rw [top_add] at h; exact absurd h (by decide)
  have hb' : b ≠ ⊤ := by rintro rfl; rw [add_top] at h; exact absurd h (by decide)
  lift a to ℕ using ha'
  lift b to ℕ using hb'
  norm_cast at *
  omega

theorem colen_eq_one_of_adjacentLattice {ϖ : R} (hϖ : Irreducible ϖ) {L L' : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (h : AdjacentLattice L L') : ϖ • L < L' ∧ L' < L ∧ colen L' L = 1 := by
  obtain ⟨ϖ', hϖ', h1, h2⟩ := h
  rw [← pointwise_smul_eq_latticeMap hϖ'.ne_zero] at h1
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ' hϖ
  have hϖϖ' : ϖ • L = ϖ' • L := by rw [← hu, mul_comm, unit_mul_smul_eq]
  rw [← hϖϖ'] at h1
  refine ⟨h1, h2, ?_⟩
  have hsum := colen_eq_add h1.le h2.le
  rw [colen_smul_eq_two hϖ hL] at hsum
  exact enat_eq_one_of_add_eq_two hsum.symm
    (fun h0 => (not_le_of_gt h2) ((colen_eq_zero_iff _ _).mp h0))
    (fun h0 => (not_le_of_gt h1) ((colen_eq_zero_iff _ _).mp h0))

theorem parity_of_adjacentLattice {ϖ : R} (hϖ : Irreducible ϖ) {L L' : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (hL' : IsFullLattice L') (h : AdjacentLattice L L') :
    parity hϖ L' hL' = parity hϖ L hL + 1 := by
  obtain ⟨_, h2, hone⟩ := colen_eq_one_of_adjacentLattice hϖ hL h
  obtain ⟨n, hn⟩ := exists_smul_le hϖ hL (isFullLattice_stdLattice (R := R) (K := K))
  have hn' : ϖ ^ n • L' ≤ ϖ ^ n • L := pointwise_smul_mono _ h2.le
  rw [parity_eq hϖ hL hn, parity_eq hϖ hL' (hn'.trans hn), parityAt, parityAt, colen_eq_add hn' hn,
    colen_pointwise_smul (pow_ne_zero n hϖ.ne_zero), hone,
    ENat.toNat_add (colen_ne_top hϖ (isFullLattice_pointwise_smul (pow_ne_zero n hϖ.ne_zero) hL)
      isFullLattice_stdLattice hn) ENat.one_ne_top, Nat.cast_add]
  simp

noncomputable def vertexParity {ϖ : R} (hϖ : Irreducible ϖ) : Vertex R K → ZMod 2 :=
  Quotient.lift (fun L : FullLattice R K => parity hϖ L.1 L.2)
    (fun L L' h => parity_eq_of_homothetic hϖ L.2 L'.2 h)

theorem vertexParity_mk {ϖ : R} (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    vertexParity hϖ (Vertex.mk R K L hL) = parity hϖ L hL := rfl

theorem vertexParity_of_vertRel {ϖ : R} (hϖ : Irreducible ϖ) {x y : Vertex R K} (h : VertRel R K x y) :
    vertexParity hϖ y = vertexParity hϖ x + 1 := by
  obtain ⟨L, L', hL, hL', rfl, rfl, hadj⟩ := h
  rw [vertexParity_mk, vertexParity_mk]
  exact parity_of_adjacentLattice hϖ hL hL' hadj

noncomputable def treeColoring {ϖ : R} (hϖ : Irreducible ϖ) : (tree R K).Coloring (ZMod 2) :=
  SimpleGraph.Coloring.mk (vertexParity hϖ) (by
    intro x y hxy
    rw [tree_adj_iff] at hxy
    have key : ∀ a : ZMod 2, a ≠ a + 1 := by decide
    rcases hxy.2 with h | h
    · rw [vertexParity_of_vertRel hϖ h]; exact key _
    · rw [vertexParity_of_vertRel hϖ h]; exact (key _).symm)

theorem tree_colorable_two : (tree R K).Colorable 2 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  simpa using (treeColoring (K := K) hϖ).colorable

end Colouring

theorem tree_connected_and_colorable_two'
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    (tree R K).Connected ∧ (tree R K).Colorable 2 :=
  ⟨tree_connected, tree_colorable_two⟩

section GraphRank

variable {W : Type*} {G : SimpleGraph W}

theorem isAcyclic_of_rank (d : W → ℕ)
    (hadj : ∀ ⦃u v : W⦄, G.Adj u v → d v + 1 = d u ∨ d u + 1 = d v)
    (huniq : ∀ ⦃u v w : W⦄, G.Adj u v → G.Adj u w → d v < d u → d w < d u → v = w) : G.IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨u, hu, hmax⟩ := c.support.toFinset.exists_max_image d ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  rw [List.mem_toFinset] at hu
  have hc' : (c.rotate u hu).IsCycle := hc.rotate hu
  have hnil : ¬ (c.rotate u hu).Nil := hc'.not_nil
  have h1 : G.Adj u (c.rotate u hu).snd := (c.rotate u hu).adj_snd hnil
  have h2 : G.Adj (c.rotate u hu).penultimate u := (c.rotate u hu).adj_penultimate hnil
  have hne : (c.rotate u hu).snd ≠ (c.rotate u hu).penultimate := hc'.snd_ne_penultimate
  have hs : (c.rotate u hu).snd ∈ c.support :=
    (c.mem_support_rotate_iff u hu).mp ((c.rotate u hu).getVert_mem_support 1)
  have hp : (c.rotate u hu).penultimate ∈ c.support :=
    (c.mem_support_rotate_iff u hu).mp ((c.rotate u hu).getVert_mem_support _)
  have hds : d (c.rotate u hu).snd < d u := by
    have := hmax _ (List.mem_toFinset.mpr hs)
    rcases hadj h1 with h | h <;> omega
  have hdp : d (c.rotate u hu).penultimate < d u := by
    have := hmax _ (List.mem_toFinset.mpr hp)
    rcases hadj h2.symm with h | h <;> omega
  exact hne (huniq h1 h2.symm hds hdp)

end GraphRank

section Rank

open LT.LatticeTree Submodule

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDiscreteValuationRing R] in
theorem pointwise_smul_cancel {r : R} (hr : r ≠ 0) {A B : Submodule R (Fin 2 → K)} (h : r • A = r • B) : A = B := by
  have hinj : Function.Injective (DistribSMul.toLinearMap R (Fin 2 → K) r) := by
    intro x y hxy
    simp only [DistribSMul.toLinearMap_apply] at hxy
    rw [← algebraMap_smul K r x, ← algebraMap_smul K r y] at hxy
    exact smul_right_injective (Fin 2 → K)
      (fun h => hr (IsFractionRing.injective R K (by rw [h, map_zero]))) hxy
  have hmap : ∀ C : Submodule R (Fin 2 → K), C.map (DistribSMul.toLinearMap R (Fin 2 → K) r) = r • C := by
    intro C; ext x
    simp only [Submodule.mem_map, DistribSMul.toLinearMap_apply, Submodule.mem_smul_pointwise_iff_exists]
  apply Submodule.map_injective_of_injective hinj
  rw [hmap, hmap, h]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem colen_latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K) (N L : Submodule R (Fin 2 → K)) :
    colen (latticeMap g N) (latticeMap g L) = colen N L := by
  apply colen_map
  intro x y hxy
  simp only [mulVecLinR_apply] at hxy
  have := congrArg (fun v => Matrix.mulVec ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) v) hxy
  simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] using this

theorem colen_pow_smul_of_le {ϖ : R} (hϖ : Irreducible ϖ) {M P : Submodule R (Fin 2 → K)} (hM : IsFullLattice M)
    (hMP : M ≤ P) (k : ℕ) : colen (ϖ ^ k • M) P = colen M P + 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : ϖ ^ k • M ≤ P := (pointwise_smul_le_self _ _).trans hMP
    rw [colen_pow_succ_smul hϖ hM k hle, ih, add_assoc]
    push_cast
    ring

theorem eq_pow_smul_of_homothetic_of_primitive {ϖ : R} (hϖ : Irreducible ϖ) {M M' : Submodule R (Fin 2 → K)}
    (hprim : ¬ M ≤ ϖ • stdLattice R K) (hM' : M' ≤ stdLattice R K) (h : Homothetic M M') :
    ∃ k : ℕ, M' = ϖ ^ k • M := by
  obtain ⟨i, j, hij⟩ := exists_pow_smul_eq_of_homothetic hϖ h

  rcases Nat.lt_or_ge i j with hij' | hji
  swap
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
    refine ⟨k, pointwise_smul_cancel (pow_ne_zero j hϖ.ne_zero) ?_⟩
    rw [hij, pow_add, mul_smul]
  · exfalso
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij'
    apply hprim
    have h2 : M = ϖ ^ (k + 1) • M' := by
      apply pointwise_smul_cancel (pow_ne_zero i hϖ.ne_zero)
      rw [← hij, show i + k + 1 = i + (k + 1) from by ring, pow_add, mul_smul]
    rw [h2, pow_succ', mul_smul]
    exact pointwise_smul_mono ϖ ((pointwise_smul_le_self _ _).trans hM')

def HasRepColen (L : Submodule R (Fin 2 → K)) (n : ℕ) : Prop :=
  ∃ M : Submodule R (Fin 2 → K), IsFullLattice M ∧ Homothetic L M ∧ M ≤ stdLattice R K ∧
    colen M (stdLattice R K) = n

theorem exists_hasRepColen {ϖ : R} (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∃ n : ℕ, HasRepColen L n := by
  obtain ⟨m, hm⟩ := exists_smul_le hϖ hL (isFullLattice_stdLattice (R := R) (K := K))
  have hfull := isFullLattice_pointwise_smul (pow_ne_zero m hϖ.ne_zero) hL
  refine ⟨(colen (ϖ ^ m • L) (stdLattice R K)).toNat, ϖ ^ m • L, hfull,
    homothetic_pointwise_smul (pow_ne_zero m hϖ.ne_zero) L, hm, ?_⟩
  rw [ENat.coe_toNat (colen_ne_top hϖ hfull isFullLattice_stdLattice hm)]

open Classical in

noncomputable def rank {ϖ : R} (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) : ℕ :=
  Nat.find (exists_hasRepColen hϖ hL)

theorem rank_spec {ϖ : R} (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    HasRepColen L (rank hϖ L hL) := by
  classical
  exact Nat.find_spec (exists_hasRepColen hϖ hL)

theorem rank_le {ϖ : R} (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) {n : ℕ}
    (h : HasRepColen L n) : rank hϖ L hL ≤ n := by
  classical
  exact Nat.find_min' _ h

omit [IsDiscreteValuationRing R] in
theorem hasRepColen_of_homothetic {L L' : Submodule R (Fin 2 → K)} (h : Homothetic L L') {n : ℕ}
    (hn : HasRepColen L' n) : HasRepColen L n := by
  obtain ⟨M, hM, hLM, hML₀, hc⟩ := hn
  exact ⟨M, hM, h.trans hLM, hML₀, hc⟩

theorem rank_eq_of_homothetic {ϖ : R} (hϖ : Irreducible ϖ) {L L' : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (hL' : IsFullLattice L') (h : Homothetic L L') : rank hϖ L hL = rank hϖ L' hL' :=
  le_antisymm (rank_le hϖ hL (hasRepColen_of_homothetic h (rank_spec hϖ hL')))
    (rank_le hϖ hL' (hasRepColen_of_homothetic h.symm (rank_spec hϖ hL)))

theorem not_le_smul_of_colen_eq_rank {ϖ : R} (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (hM : IsFullLattice M) (hLM : Homothetic L M) (hML₀ : M ≤ stdLattice R K)
    (hc : colen M (stdLattice R K) = rank hϖ L hL) : ¬ M ≤ ϖ • stdLattice R K := by
  intro hle
  obtain ⟨M₁, hM₁, hhom, hϖM₁, hM₁L₀⟩ := exists_smul_eq_of_le_smul hϖ hM hle
  have h1 : colen M (stdLattice R K) = colen M₁ (stdLattice R K) + 2 := by
    rw [← hϖM₁, colen_eq_add (pointwise_smul_le_self ϖ M₁) hM₁L₀, colen_smul_eq_two hϖ hM₁]
  have hfin : colen M₁ (stdLattice R K) ≠ ⊤ := colen_ne_top hϖ hM₁ isFullLattice_stdLattice hM₁L₀
  have h2 : HasRepColen L (colen M₁ (stdLattice R K)).toNat :=
    ⟨M₁, hM₁, hLM.trans hhom, hM₁L₀, by rw [ENat.coe_toNat hfin]⟩
  have h3 := rank_le hϖ hL h2

  have h4 : (rank hϖ L hL : ℕ∞) = (colen M₁ (stdLattice R K)).toNat + 2 := by
    rw [← hc, h1, ENat.coe_toNat hfin]
  have : (rank hϖ L hL : ℕ) = (colen M₁ (stdLattice R K)).toNat + 2 := by exact_mod_cast h4
  omega

theorem exists_primitive_rep {ϖ : R} (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) :
    ∃ M : Submodule R (Fin 2 → K), IsFullLattice M ∧ Homothetic L M ∧ M ≤ stdLattice R K ∧
      ¬ M ≤ ϖ • stdLattice R K ∧ colen M (stdLattice R K) = rank hϖ L hL := by
  obtain ⟨M, hM, hLM, hML₀, hc⟩ := rank_spec hϖ hL
  exact ⟨M, hM, hLM, hML₀, not_le_smul_of_colen_eq_rank hϖ hL hM hLM hML₀ hc, hc⟩

theorem rank_eq_colen_of_primitive {ϖ : R} (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (hM : IsFullLattice M) (hLM : Homothetic L M) (hML₀ : M ≤ stdLattice R K)
    (hprim : ¬ M ≤ ϖ • stdLattice R K) : (rank hϖ L hL : ℕ∞) = colen M (stdLattice R K) := by
  obtain ⟨M', hM', hLM', hM'L₀, hc⟩ := rank_spec hϖ hL
  obtain ⟨k, rfl⟩ := eq_pow_smul_of_homothetic_of_primitive hϖ hprim hM'L₀ (hLM.symm.trans hLM')
  rw [colen_pow_smul_of_le hϖ hM hML₀] at hc
  have hfin : colen M (stdLattice R K) ≠ ⊤ := colen_ne_top hϖ hM isFullLattice_stdLattice hML₀
  have hle : rank hϖ L hL ≤ (colen M (stdLattice R K)).toNat :=
    rank_le hϖ hL ⟨M, hM, hLM, hML₀, by rw [ENat.coe_toNat hfin]⟩
  apply le_antisymm
  · calc (rank hϖ L hL : ℕ∞) ≤ ((colen M (stdLattice R K)).toNat : ℕ∞) := by exact_mod_cast hle
      _ = colen M (stdLattice R K) := ENat.coe_toNat hfin
  · rw [← hc]; exact le_self_add

noncomputable def vertexRank {ϖ : R} (hϖ : Irreducible ϖ) : Vertex R K → ℕ :=
  Quotient.lift (fun L : FullLattice R K => rank hϖ L.1 L.2)
    (fun L L' h => rank_eq_of_homothetic hϖ L.2 L'.2 h)

theorem vertexRank_mk {ϖ : R} (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    vertexRank hϖ (Vertex.mk R K L hL) = rank hϖ L hL := rfl

theorem vertexParity_eq_rank {ϖ : R} (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    vertexParity hϖ (Vertex.mk R K L hL) = (rank hϖ L hL : ZMod 2) := by
  obtain ⟨M, hM, hLM, hML₀, -, hc⟩ := exists_primitive_rep hϖ hL
  rw [show Vertex.mk R K L hL = Vertex.mk R K M hM from Vertex.mk_eq_mk_iff.mpr hLM, vertexParity_mk,
    parity_eq hϖ hM (n := 0) (by rwa [pow_zero, one_smul]), parityAt, pow_zero, one_smul, hc]
  simp

theorem enat_eq_zero_of_add_eq_one {a b : ℕ∞} (h : a + b = 1) (ha : a ≠ 0) : b = 0 := by
  have ha' : a ≠ ⊤ := by rintro rfl; rw [top_add] at h; exact absurd h (by decide)
  have hb' : b ≠ ⊤ := by rintro rfl; rw [add_top] at h; exact absurd h (by decide)
  lift a to ℕ using ha'
  lift b to ℕ using hb'
  norm_cast at *
  omega

theorem exists_reps_of_adj {ϖ : R} (hϖ : Irreducible ϖ) {x y : Vertex R K} (h : (tree R K).Adj x y) :
    ∃ (L L' : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) (hL' : IsFullLattice L'),
      Vertex.mk R K L hL = x ∧ Vertex.mk R K L' hL' = y ∧ ϖ • L < L' ∧ L' < L := by
  rw [tree_adj_iff] at h
  rcases h.2 with ⟨L, L', hL, hL', rfl, rfl, hadj⟩ | ⟨L', L, hL', hL, rfl, rfl, hadj⟩
  · obtain ⟨h1, h2, -⟩ := colen_eq_one_of_adjacentLattice hϖ hL hadj
    exact ⟨L, L', hL, hL', rfl, rfl, h1, h2⟩
  ·
    obtain ⟨h1, h2, -⟩ := colen_eq_one_of_adjacentLattice hϖ hL' hadj
    refine ⟨L, ϖ • L', hL, isFullLattice_pointwise_smul hϖ.ne_zero hL', rfl,
      (Vertex.mk_eq_mk_iff.mpr (homothetic_pointwise_smul hϖ.ne_zero L')).symm, ?_, h1⟩
    refine lt_of_le_of_ne (pointwise_smul_mono ϖ h2.le) (fun heq => h2.ne (pointwise_smul_cancel hϖ.ne_zero heq))

theorem exists_rep_between_of_adj {ϖ : R} (hϖ : Irreducible ϖ) {x y : Vertex R K} (h : (tree R K).Adj x y)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) (hx : Vertex.mk R K L hL = x) :
    ∃ (L' : Submodule R (Fin 2 → K)) (hL' : IsFullLattice L'), Vertex.mk R K L' hL' = y ∧ ϖ • L < L' ∧ L' < L := by
  obtain ⟨L₁, L₁', hL₁, hL₁', rfl, rfl, h1, h2⟩ := exists_reps_of_adj hϖ h
  obtain ⟨c, rfl⟩ : Homothetic L₁ L := Vertex.mk_eq_mk_iff.mp hx.symm
  refine ⟨latticeMap (scalarGL c) L₁', hL₁'.map _, (Vertex.mk_eq_mk_iff.mpr ⟨c, rfl⟩).symm, ?_,
    (latticeMap_lt_latticeMap_iff _).mpr h2⟩
  have : ϖ • latticeMap (scalarGL c) L₁ = latticeMap (scalarGL c) (ϖ • L₁) := by
    rw [pointwise_smul_eq_latticeMap hϖ.ne_zero, pointwise_smul_eq_latticeMap hϖ.ne_zero, ← latticeMap_mul,
      ← latticeMap_mul, scalarGL_mul_comm]
  rw [this]
  exact (latticeMap_lt_latticeMap_iff _).mpr h1

theorem rank_adj {ϖ : R} (hϖ : Irreducible ϖ) {x y : Vertex R K} (h : (tree R K).Adj x y) :
    vertexRank hϖ y + 1 = vertexRank hϖ x ∨ vertexRank hϖ x + 1 = vertexRank hϖ y := by
  induction x using Quotient.inductionOn with | h Lx => ?_
  obtain ⟨L, hL, hxL, hLL₀, hprim, hcL⟩ := exists_primitive_rep hϖ Lx.2
  have hx : Vertex.mk R K L hL = Vertex.mk R K Lx.1 Lx.2 := (Vertex.mk_eq_mk_iff.mpr hxL).symm
  obtain ⟨L', hL', rfl, h1, h2⟩ := exists_rep_between_of_adj hϖ h hL hx
  change rank hϖ L' hL' + 1 = rank hϖ Lx.1 Lx.2 ∨ rank hϖ Lx.1 Lx.2 + 1 = rank hϖ L' hL'
  have hrank : rank hϖ Lx.1 Lx.2 = rank hϖ L hL := rank_eq_of_homothetic hϖ Lx.2 hL hxL
  rw [hrank] at hcL ⊢
  set n := rank hϖ L hL with hn
  set m := rank hϖ L' hL' with hm

  have hsum := colen_eq_add h1.le h2.le
  rw [colen_smul_eq_two hϖ hL] at hsum
  have hone : colen L' L = 1 := enat_eq_one_of_add_eq_two hsum.symm
    (fun h0 => (not_le_of_gt h2) ((colen_eq_zero_iff _ _).mp h0))
    (fun h0 => (not_le_of_gt h1) ((colen_eq_zero_iff _ _).mp h0))
  have hone' : colen (ϖ • L) L' = 1 := by
    rw [hone] at hsum
    exact enat_eq_one_of_add_eq_two ((add_comm _ _).trans hsum.symm)
      (fun h0 => (not_le_of_gt h1) ((colen_eq_zero_iff _ _).mp h0)) one_ne_zero

  have hi : m ≤ n + 1 := by
    apply rank_le hϖ hL'
    refine ⟨L', hL', Homothetic.refl _, h2.le.trans hLL₀, ?_⟩
    rw [colen_eq_add h2.le hLL₀, hcL, hone]
    norm_cast

  have hii : n ≤ m + 1 := by
    obtain ⟨M', hM', hL'M', hM'L₀, -, hcM'⟩ := exists_primitive_rep hϖ hL'
    obtain ⟨c, rfl⟩ := hL'M'

    have hlt : latticeMap (scalarGL c) (ϖ • L) < latticeMap (scalarGL c) L' := (latticeMap_lt_latticeMap_iff _).mpr h1
    rw [← hrank]
    apply rank_le hϖ Lx.2
    refine ⟨latticeMap (scalarGL c) (ϖ • L), (isFullLattice_pointwise_smul hϖ.ne_zero hL).map _,
      (hxL.trans (homothetic_pointwise_smul hϖ.ne_zero L)).trans ⟨c, rfl⟩, hlt.le.trans hM'L₀, ?_⟩
    rw [colen_eq_add hlt.le hM'L₀, hcM', colen_latticeMap, hone']
    norm_cast

  have hiii : m ≠ n := by
    intro hmn
    have hpar := vertexParity_of_vertRel hϖ (x := Vertex.mk R K L hL) (y := Vertex.mk R K L' hL')
      ⟨L, L', hL, hL', rfl, rfl, ϖ, hϖ, by rwa [← pointwise_smul_eq_latticeMap], h2⟩
    rw [vertexParity_eq_rank, vertexParity_eq_rank, ← hm, ← hn, hmn] at hpar
    have key : ∀ a : ZMod 2, a ≠ a + 1 := by decide
    exact key _ hpar
  omega

theorem eq_inf_of_rank_lt {ϖ : R} (hϖ : Irreducible ϖ) {L L' : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (hL' : IsFullLattice L') (hLL₀ : L ≤ stdLattice R K) (hprim : ¬ L ≤ ϖ • stdLattice R K)
    (hcL : colen L (stdLattice R K) = rank hϖ L hL) (h1 : ϖ • L < L') (h2 : L' < L)
    (hlt : rank hϖ L' hL' + 1 = rank hϖ L hL) : L' = L ⊓ ϖ • stdLattice R K := by

  have hsum := colen_eq_add h1.le h2.le
  rw [colen_smul_eq_two hϖ hL] at hsum
  have hone : colen L' L = 1 := enat_eq_one_of_add_eq_two hsum.symm
    (fun h0 => (not_le_of_gt h2) ((colen_eq_zero_iff _ _).mp h0))
    (fun h0 => (not_le_of_gt h1) ((colen_eq_zero_iff _ _).mp h0))

  obtain ⟨M', hM', hL'M', hM'L₀, hprim', hcM'⟩ := exists_primitive_rep hϖ hL'
  obtain ⟨k, hk⟩ := eq_pow_smul_of_homothetic_of_primitive hϖ hprim' (h2.le.trans hLL₀) hL'M'.symm
  have hcL' : colen L' (stdLattice R K) = rank hϖ L hL + 1 := by
    rw [colen_eq_add h2.le hLL₀, hcL, hone]
  have hcL'' : colen L' (stdLattice R K) = rank hϖ L' hL' + 2 * k := by
    conv_lhs => rw [hk]
    rw [colen_pow_smul_of_le hϖ hM' hM'L₀ k, hcM']
  have hk1 : k = 1 := by
    have : (rank hϖ L hL : ℕ∞) + 1 = rank hϖ L' hL' + 2 * k := hcL'.symm.trans hcL''
    have : rank hϖ L hL + 1 = rank hϖ L' hL' + 2 * k := by exact_mod_cast this
    omega
  rw [hk1, pow_one] at hk

  have hle : L' ≤ L ⊓ ϖ • stdLattice R K := le_inf h2.le (hk ▸ pointwise_smul_mono ϖ hM'L₀)
  have hlt' : L ⊓ ϖ • stdLattice R K < L := lt_of_le_of_ne inf_le_left (fun h => hprim (inf_eq_left.mp h))
  have hsplit := colen_eq_add hle hlt'.le
  rw [hone] at hsplit
  have hpos : colen (L ⊓ ϖ • stdLattice R K) L ≠ 0 :=
    fun h0 => (not_le_of_gt hlt') ((colen_eq_zero_iff _ _).mp h0)
  have hzero : colen L' (L ⊓ ϖ • stdLattice R K) = 0 := enat_eq_zero_of_add_eq_one hsplit.symm hpos
  exact le_antisymm hle ((colen_eq_zero_iff _ _).mp hzero)

end Rank

section Tree

open LT.LatticeTree Submodule

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

theorem rank_uniq {ϖ : R} (hϖ : Irreducible ϖ) {x y z : Vertex R K} (hy : (tree R K).Adj x y) (hz : (tree R K).Adj x z)
    (hdy : vertexRank hϖ y < vertexRank hϖ x) (hdz : vertexRank hϖ z < vertexRank hϖ x) : y = z := by
  have hdy' : vertexRank hϖ y + 1 = vertexRank hϖ x := by rcases rank_adj hϖ hy with h | h <;> omega
  have hdz' : vertexRank hϖ z + 1 = vertexRank hϖ x := by rcases rank_adj hϖ hz with h | h <;> omega
  clear hdy hdz
  induction x using Quotient.inductionOn with | h Lx => ?_
  obtain ⟨L, hL, hxL, hLL₀, hprim, hcL⟩ := exists_primitive_rep hϖ Lx.2
  have hx : Vertex.mk R K L hL = Vertex.mk R K Lx.1 Lx.2 := (Vertex.mk_eq_mk_iff.mpr hxL).symm
  obtain ⟨Ly, hLy, rfl, hy1, hy2⟩ := exists_rep_between_of_adj hϖ hy hL hx
  obtain ⟨Lz, hLz, rfl, hz1, hz2⟩ := exists_rep_between_of_adj hϖ hz hL hx
  change rank hϖ Ly hLy + 1 = rank hϖ Lx.1 Lx.2 at hdy'
  change rank hϖ Lz hLz + 1 = rank hϖ Lx.1 Lx.2 at hdz'
  rw [rank_eq_of_homothetic hϖ Lx.2 hL hxL] at hdy' hdz' hcL
  have ey := eq_inf_of_rank_lt hϖ hL hLy hLL₀ hprim hcL hy1 hy2 hdy'
  have ez := eq_inf_of_rank_lt hϖ hL hLz hLL₀ hprim hcL hz1 hz2 hdz'
  subst ey
  subst ez
  rfl

theorem tree_isAcyclic : (tree R K).IsAcyclic := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact isAcyclic_of_rank (vertexRank (K := K) hϖ) (fun _ _ h => rank_adj hϖ h)
    (fun _ _ _ h1 h2 h3 h4 => rank_uniq hϖ h1 h2 h3 h4)

end Tree

theorem tree_isTree'
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    (tree R K).IsTree :=
  ⟨tree_connected, tree_isAcyclic⟩

end CerednikDrinfeld.BruhatTits.TreeCC
p2m_reactivate "P2MW.S_CerednikDrinfeld_BruhatTits_tree_isTree.CerednikDrinfeld P2MW.S_CerednikDrinfeld_BruhatTits_tree_isTree.CerednikDrinfeld.BruhatTits P2MW.S_CerednikDrinfeld_BruhatTits_tree_isTree.CerednikDrinfeld.BruhatTits.TreeCC"
p2m_reactivate "P2MW.S_CerednikDrinfeld_BruhatTits_tree_isTree.CerednikDrinfeld P2MW.S_CerednikDrinfeld_BruhatTits_tree_isTree.CerednikDrinfeld.BruhatTits"
p2m_reactivate "P2MW.S_CerednikDrinfeld_BruhatTits_tree_isTree.CerednikDrinfeld"

p2m_open "CerednikDrinfeld.BruhatTits P2MW.S_CerednikDrinfeld_BruhatTits_tree_isTree.CerednikDrinfeld.BruhatTits LT.LatticeTree"

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    (tree R K).IsTree :=
  CerednikDrinfeld.BruhatTits.TreeCC.tree_isTree' R K

end S_CerednikDrinfeld_BruhatTits_tree_isTree
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_tree_isTree (solution)
