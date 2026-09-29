-- Prove2me | solution 1 for CerednikDrinfeld.BruhatTits.faithfulSMul_projGenLinGroup_vertex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/adf8c5d0-2563-508f-9a20-a0ad6932af1a

import Mathlib
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "pgl_mk_smul tree"
namespace BruhatTits
p2m_export "CerednikDrinfeld.BruhatTits" "tree pgl_mk_smul"
namespace FaithfulQ3
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

section Scaling

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

theorem colen_pow_smul_of_le {ϖ : R} (hϖ : Irreducible ϖ) {M P : Submodule R (Fin 2 → K)} (hM : IsFullLattice M)
    (hMP : M ≤ P) (k : ℕ) : colen (ϖ ^ k • M) P = colen M P + 2 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : ϖ ^ k • M ≤ P := (pointwise_smul_le_self _ _).trans hMP
    rw [colen_pow_succ_smul hϖ hM k hle, ih, add_assoc]
    push_cast
    ring

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

end Scaling

section Faithful

open LT.LatticeTree Submodule

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

theorem latticeMap_eq_self_of_forall_fixed {ϖ : R} (hϖ : Irreducible ϖ) (M : Matrix.GeneralLinearGroup (Fin 2) R)
    (hfix : ∀ v : Vertex R K, Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap R K) M) v = v)
    {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L) (hLL₀ : L ≤ stdLattice R K) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M) L = L := by
  set h := Matrix.GeneralLinearGroup.map (algebraMap R K) M with hh
  have hL₀ : latticeMap h (stdLattice R K) = stdLattice R K :=
    (latticeMap_stdLattice_eq_iff_mem_range h).mpr ⟨M, rfl⟩
  have hhom : Homothetic (latticeMap h L) L := by
    have := hfix (Vertex.mk R K L hL)
    rwa [Vertex.act_mk, Vertex.mk_eq_mk_iff] at this
  obtain ⟨i, j, hij⟩ := exists_pow_smul_eq_of_homothetic hϖ hhom

  have hle : latticeMap h L ≤ stdLattice R K := by
    rw [← hL₀]; exact latticeMap_mono h hLL₀
  have hfull : IsFullLattice (latticeMap h L) := hL.map h
  have hc : colen (latticeMap h L) (stdLattice R K) = colen L (stdLattice R K) := by
    conv_lhs => rw [← hL₀]
    exact colen_latticeMap h L _
  have h1 := colen_pow_smul_of_le hϖ hL hLL₀ j
  have h2 := colen_pow_smul_of_le hϖ hfull hle i
  rw [hij, h2, hc] at h1
  have hfin := colen_ne_top hϖ hL isFullLattice_stdLattice hLL₀
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [← hm] at h1
  have hij' : i = j := by
    have : (m : ℕ) + 2 * i = m + 2 * j := by exact_mod_cast h1
    omega
  rw [hij'] at hij
  exact (pointwise_smul_cancel (pow_ne_zero j hϖ.ne_zero) hij).symm

theorem pow_dvd_entries {ϖ : R} (hϖ : Irreducible ϖ) (M : Matrix.GeneralLinearGroup (Fin 2) R)
    (hfix : ∀ v : Vertex R K, Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap R K) M) v = v) (n : ℕ) :
    ϖ ^ n ∣ (M : Matrix (Fin 2) (Fin 2) R) 1 0 ∧ ϖ ^ n ∣ (M : Matrix (Fin 2) (Fin 2) R) 0 1 ∧
      ϖ ^ n ∣ ((M : Matrix (Fin 2) (Fin 2) R) 0 0 + (M : Matrix (Fin 2) (Fin 2) R) 0 1) -
        ((M : Matrix (Fin 2) (Fin 2) R) 1 0 + (M : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  have hn : ϖ ^ n ≠ 0 := pow_ne_zero n hϖ.ne_zero
  have full : ∀ c d : R, IsFullLattice (interLattice R K (ϖ ^ n) c d) := fun c d =>
    isFullLattice_of_le_of_le hn (latticeMap_scalarGL_le_interLattice hn c d) (interLattice_le_stdLattice _ _ _)
  have key : ∀ c d : R, ϖ ^ n ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 := fun c d =>
    dvd_of_latticeMap_map_interLattice_eq_self M
      (latticeMap_eq_self_of_forall_fixed hϖ M hfix (full c d) (interLattice_le_stdLattice _ _ _))
  refine ⟨?_, ?_, ?_⟩
  · have := key 1 0
    simp only [mulVecPair_zero, mulVecPair_one, mul_one, mul_zero, add_zero, zero_mul, zero_sub, one_mul,
      dvd_neg] at this
    exact this
  · have := key 0 1
    simp only [mulVecPair_zero, mulVecPair_one, mul_one, mul_zero, zero_add, zero_mul, sub_zero, one_mul] at this
    exact this
  · have := key 1 1
    simp only [mulVecPair_zero, mulVecPair_one, mul_one, one_mul] at this
    exact this

theorem eq_zero_of_forall_pow_dvd {ϖ : R} (hϖ : Irreducible ϖ) {x : R} (h : ∀ n : ℕ, ϖ ^ n ∣ x) : x = 0 := by
  by_contra hx
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  have h1 := h (n + 1)
  rw [pow_succ, mul_comm (u : R), mul_dvd_mul_iff_left (pow_ne_zero n hϖ.ne_zero)] at h1
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h1 u.isUnit)

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem scalarGL_inv (c : Kˣ) : (scalarGL c)⁻¹ = scalarGL c⁻¹ := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← scalarGL_mul, inv_mul_cancel, scalarGL_one]

theorem mem_center_of_forall_fixed {ϖ : R} (hϖ : Irreducible ϖ) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfix : ∀ v : Vertex R K, g • v = v) : g ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) := by
  obtain ⟨c, M, hM⟩ := (Vertex.act_stdVertex_eq_iff g).mp (hfix (stdVertex R K))

  have hfixM : ∀ v : Vertex R K, Vertex.act (Matrix.GeneralLinearGroup.map (algebraMap R K) M) v = v := by
    intro v
    rw [hM, Vertex.act_mul]
    change Vertex.act (scalarGL c) (g • v) = v
    rw [hfix v]
    exact isFixedVertex_scalarGL c v
  have h10 : (M : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 :=
    eq_zero_of_forall_pow_dvd hϖ (fun n => (pow_dvd_entries hϖ M hfixM n).1)
  have h01 : (M : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 :=
    eq_zero_of_forall_pow_dvd hϖ (fun n => (pow_dvd_entries hϖ M hfixM n).2.1)
  have hdiag : (M : Matrix (Fin 2) (Fin 2) R) 0 0 = (M : Matrix (Fin 2) (Fin 2) R) 1 1 := by
    apply sub_eq_zero.mp
    apply eq_zero_of_forall_pow_dvd hϖ
    intro n
    have := (pow_dvd_entries hϖ M hfixM n).2.2
    rwa [h10, h01, add_zero, zero_add] at this
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨((c⁻¹ : Kˣ) : K) * algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 0 0), ?_⟩
  have hg : g = (scalarGL c)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap R K) M := by
    rw [hM, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hg, scalarGL_inv, Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, Matrix.scalar_apply]
  ext i j
  rw [Matrix.smul_apply, map_coe_apply, Matrix.diagonal_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [h10, h01, hdiag]

theorem faithfulSMul_projGenLinGroup_vertex' : FaithfulSMul (Matrix.ProjGenLinGroup (Fin 2) K) (Vertex R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨fun {q₁ q₂} h => ?_⟩
  have h1 : ∀ v : Vertex R K, (q₂⁻¹ * q₁) • v = v := fun v => by
    rw [mul_smul, h v, ← mul_smul, inv_mul_cancel, one_smul]
  suffices hq : q₂⁻¹ * q₁ = 1 from (inv_mul_eq_one.mp hq).symm
  generalize q₂⁻¹ * q₁ = q at h1
  induction q using Matrix.ProjGenLinGroup.induction_on with | mk g => ?_
  rw [Matrix.ProjGenLinGroup.mk_eq_one]
  apply mem_center_of_forall_fixed hϖ g
  intro v
  have := h1 v
  rwa [pgl_mk_smul] at this

end Faithful

end CerednikDrinfeld.BruhatTits.FaithfulQ3
p2m_reactivate "P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex.CerednikDrinfeld P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex.CerednikDrinfeld.BruhatTits P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex.CerednikDrinfeld.BruhatTits.FaithfulQ3"
p2m_reactivate "P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex.CerednikDrinfeld P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex.CerednikDrinfeld.BruhatTits"
p2m_reactivate "P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex.CerednikDrinfeld"

p2m_open "CerednikDrinfeld.BruhatTits P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex.CerednikDrinfeld.BruhatTits LT.LatticeTree"

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] :
    FaithfulSMul (Matrix.ProjGenLinGroup (Fin 2) K) (Vertex R K) :=
  CerednikDrinfeld.BruhatTits.FaithfulQ3.faithfulSMul_projGenLinGroup_vertex'

end S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex
end P2MW
export P2MW.S_CerednikDrinfeld_BruhatTits_faithfulSMul_projGenLinGroup_vertex (solution)
