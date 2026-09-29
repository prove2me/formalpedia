-- Prove2me | solution 1 for Garrido.exists_isometryInvariant_finitelyAdditive_extension_volume
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T08:19:45.377491+00:00
-- url     : https://prove2.me/submissions/90b51db0-dcce-49eb-ab16-30a0724092d8

import Mathlib
import Theorems.Thm_Garrido_hasInvariantExtensionProperty_of_isAmenable
import Theorems.Thm_Garrido_isAmenable_of_isSolvable_of_finiteIndex
import Theorems.Thm_FinitelyAdditive_exists_extension_of_sFinite
import Definitions.Def_Garrido_Amenability
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Garrido_Equidecomposability
import Definitions.Def_Garrido_Foelner
import Definitions.Def_Chou_Growth

universe u v

namespace Garrido.Lib

open scoped ENNReal Pointwise Topology
open Filter Set Garrido

end Garrido.Lib

/-!
# Closure properties of amenability (Garrido, Example 2.1, Proposition 2.2(1),(3),
Corollary 2.4, and EG ⊆ AG)

Everything is proved from one pushforward lemma: if `f : G → K` satisfies, for every `k : K`,
some `g : G` with `f (g * x) = k * f x` for all `x`, then an invariant finitely additive
probability on `G` pushes forward along `f` to one on `K`. Quotient maps, isomorphisms and the
"`H`-component" map `G → H` of a right transversal all have this shape.
-/

namespace Garrido.Lib

open Garrido
open scoped ENNReal Pointwise


/-! ### Pushforward -/

/-! ### Example 2.1 -/

/-! ### Proposition 2.2(1) -/

/-! ### Proposition 2.2(3) -/


/-! ### Corollary 2.4, from Propositions 2.3 and 2.2(2) taken as hypotheses -/

section Hyp

variable (h23 : ∀ (K : Type u) [CommGroup K], IsAmenable K)
  (h222 : ∀ (K : Type u) [Group K] (N : Subgroup K) [N.Normal],
    IsAmenable N → IsAmenable (K ⧸ N) → IsAmenable K)
include h23 h222

end Hyp

end Garrido.Lib

/-!
# Means versus finitely additive measures (Garrido, Theorem 1.15 and Proposition 2.2(2))

From a finitely additive probability measure `m` on `X` we build the integral
`mean_integral m : ℓ∞(X) →ₗ[ℝ] ℝ`. It is the upper Darboux integral
`f ↦ inf { ∫ s dm : s finitely valued, f ≤ s }`, which is sublinear; Hahn–Banach gives a linear
functional below it, and uniform approximation by finitely valued functions shows that functional
equals the upper integral, so the upper integral is linear.
-/

namespace Garrido.Lib

open scoped ENNReal Pointwise
open Set


section Integral

variable {X : Type*} (m : Set X → ℝ≥0∞)

variable {m}

/-! ### The upper integral on `ℓ∞` -/

local notation "E" X => lp (fun _ : X => ℝ) ∞

/-- A finitely valued function as an element of `ℓ∞`. -/
noncomputable def meanOfFin (s : X → ℝ) (hs : (range s).Finite) : E X :=
  ⟨s, memℓp_infty_iff.2 (by
    have : (range fun i => ‖s i‖) = (fun v => ‖v‖) '' range s := by
      rw [← Set.range_comp]; rfl
    rw [this]
    exact (hs.image _).bddAbove)⟩

@[simp] theorem meanOfFin_apply (s : X → ℝ) (hs : (range s).Finite) (x : X) :
    (meanOfFin s hs : X → ℝ) x = s x := rfl

theorem mean_range_indicator (A : Set X) : (range (A.indicator (1 : X → ℝ))).Finite :=
  (Set.toFinite ({0, 1} : Set ℝ)).subset (by
    rintro _ ⟨x, rfl⟩; by_cases h : x ∈ A <;> simp [h])

/-- The indicator function of `A` as an element of `ℓ∞`. -/
noncomputable def mean_ind (A : Set X) : E X := meanOfFin _ (mean_range_indicator A)

@[simp] theorem mean_ind_apply (A : Set X) (x : X) :
    (mean_ind A : X → ℝ) x = A.indicator 1 x := rfl

end Integral

/-! ### From a mean to a measure -/

section MeanToMeasure

/-- A bounded function with values in `[0, 1]`, as an element of `ℓ∞`. -/
noncomputable def mean_ofUnit {X : Type*} (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    lp (fun _ : X => ℝ) ∞ :=
  ⟨f, memℓp_infty_iff.2 ⟨1, by
    rintro _ ⟨x, rfl⟩
    simp only [Real.norm_eq_abs, abs_of_nonneg (hf x).1]
    exact (hf x).2⟩⟩

@[simp] theorem mean_ofUnit_apply {X : Type*} (f : X → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (x : X) : (mean_ofUnit f hf : X → ℝ) x = f x := rfl

end MeanToMeasure

/-! ### Theorem 1.15 -/


/-! ### The easy half of Tarski's theorem (Theorem 1.11, ⇒) -/

/-! ### Proposition 2.2(2) -/

end Garrido.Lib

/-!
# Garrido, Theorems 2.6 and 2.7 (invariant extension property)

Construction for 2.6 (`HasInvariantMean G → HasInvariantExtensionProperty G`): with `m` a
left-invariant mean, for `b : Set X` put `f_b g := ν (g⁻¹ • b)` and
`μbar b := ofReal (m (toReal ∘ f_b))` when `f_b` is bounded by a finite constant, `∞` otherwise.
* additivity: `f_{b ∪ c} = f_b + f_c` for disjoint `b, c`; the sum is bounded iff both are,
  and otherwise both sides are `∞`;
* invariance: `f_{h • b} g = f_b (h⁻¹ * g)`, i.e. `toReal ∘ f_{h • b} = lshift h (toReal ∘ f_b)`
  (matching `lshift h f g = f (h⁻¹ * g)`);
* extension: for `s ∈ R`, `f_s` is the constant `μ s` (finite: the mean of a constant;
  infinite: unbounded, so `∞`).
-/

namespace Garrido.Lib

open Garrido
open scoped ENNReal Pointwise


/-- A function `G → ℝ≥0∞` bounded by a finite constant. -/
def ext_Bdd {G : Type*} (f : G → ℝ≥0∞) : Prop := ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ g, f g ≤ C

/-- The real-valued bounded function `toReal ∘ f`, as an element of `ℓ∞(G)`. -/
noncomputable def ext_toLp {G : Type*} (f : G → ℝ≥0∞) (hf : ext_Bdd f) :
    lp (fun _ : G => ℝ) ∞ :=
  ⟨fun g => (f g).toReal, by
    obtain ⟨C, hC, hle⟩ := hf
    refine memℓp_infty_iff.2 ⟨C.toReal, ?_⟩
    rintro _ ⟨g, rfl⟩
    simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hC (hle g)⟩

@[simp] theorem ext_toLp_apply {G : Type*} (f : G → ℝ≥0∞) (hf : ext_Bdd f) (g : G) :
    (ext_toLp f hf : G → ℝ) g = (f g).toReal := rfl

end Garrido.Lib

namespace Garrido.Lib

open scoped ENNReal Pointwise symmDiff Topology
open MeasureTheory Filter Set


section Growth

variable {G : Type*} [Group G]

end Growth

end Garrido.Lib

namespace Garrido.Lib

open scoped Pointwise symmDiff ENNReal
open Finset

section Layer

variable {G : Type*} [Group G] [DecidableEq G]

end Layer

section Mean

variable {G : Type*} [Group G]

end Mean


end Garrido.Lib

namespace Garrido.Lib

open scoped ENNReal Pointwise
open Set

end Garrido.Lib

namespace Garrido.Lib

open scoped ENNReal Pointwise
open Set

end Garrido.Lib

namespace Garrido.Lib

open Garrido MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise

section Extension

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

open Classical


/-- The recalled Carathéodory-type fact: an s-finite measure extends to a finitely additive
measure on all subsets. -/
theorem leb_exists_finitelyAdditive_extension [SFinite μ] :
    ∃ ν : Set X → ℝ≥0∞, IsFinitelyAdditiveMeasure ν ∧
      ∀ s, NullMeasurableSet s μ → ν s = μ s := by
  obtain ⟨ν, h0, hadd, hμ⟩ := FinitelyAdditive.exists_extension_of_sFinite μ
  exact ⟨ν, ⟨h0, hadd⟩, hμ⟩

end Extension

end Garrido.Lib

namespace Garrido.Lib

open Garrido MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise

section Isometry

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-- The linear part of an isometry: `v ↦ f v - f 0` (linear by Mazur–Ulam). -/
noncomputable def leb_lin (f : (E n) ≃ᵢ (E n)) : (E n) ≃ₗᵢ[ℝ] (E n) :=
  f.toRealAffineIsometryEquiv.linearIsometryEquiv

theorem leb_lin_apply (f : (E n) ≃ᵢ (E n)) (v : E n) : leb_lin f v = f v - f 0 := by
  have := f.toRealAffineIsometryEquiv.map_vsub v 0
  simpa [leb_lin] using this

theorem leb_apply_eq (f : (E n) ≃ᵢ (E n)) (v : E n) : f v = leb_lin f v + f 0 := by
  rw [leb_lin_apply]; abel

/-- The linear-part homomorphism. -/
noncomputable def leb_linHom : ((E n) ≃ᵢ (E n)) →* ((E n) ≃ₗᵢ[ℝ] (E n)) where
  toFun := leb_lin
  map_one' := by ext v; simp [leb_lin_apply]
  map_mul' f g := by
    refine LinearIsometryEquiv.ext fun v => ?_
    show leb_lin (f * g) v = leb_lin f (leb_lin g v)
    rw [leb_lin_apply g, map_sub]
    simp only [leb_lin_apply, IsometryEquiv.mul_apply]
    abel

/-- Translations. -/
noncomputable def leb_transHom : Multiplicative (E n) →* ((E n) ≃ᵢ (E n)) where
  toFun a := IsometryEquiv.addRight a.toAdd
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp [add_assoc, add_comm (a.toAdd)]

theorem leb_ker_le_range :
    (leb_linHom (n := n)).ker ≤ (leb_transHom (n := n)).range := by
  intro f hf
  refine ⟨Multiplicative.ofAdd (f 0), ?_⟩
  ext v
  have : leb_lin f = 1 := hf
  simp [leb_transHom, leb_apply_eq f v, this]

theorem leb_linear_comm_of_le_one (hn : n ≤ 1) (f g : (E n) ≃ₗᵢ[ℝ] (E n)) :
    f * g = g * f := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn with rfl | rfl
  · exact LinearIsometryEquiv.ext fun v => Subsingleton.elim _ _
  · have hd : Module.finrank ℝ (E 1) = 1 := by simp
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd
      (f.toLinearEquiv : (E 1) →ₗ[ℝ] (E 1))
    obtain ⟨d, hd', -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd
      (g.toLinearEquiv : (E 1) →ₗ[ℝ] (E 1))
    have hf : ∀ v, f v = c • v := fun v => by
      have := LinearMap.congr_fun hc v; simpa using this
    have hg : ∀ v, g v = d • v := fun v => by
      have := LinearMap.congr_fun hd' v; simpa using this
    refine LinearIsometryEquiv.ext fun v => ?_
    simp [LinearIsometryEquiv.coe_mul, hf, hg, smul_smul, mul_comm]

/-- The determinant homomorphism on linear isometries. -/
noncomputable def leb_detHom : ((E n) ≃ₗᵢ[ℝ] (E n)) →* ℝˣ :=
  LinearEquiv.det.comp
    { toFun := fun f => f.toLinearEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem leb_rot_comm (f g : (E 2) ≃ₗᵢ[ℝ] (E 2)) (hf : leb_detHom f = 1)
    (hg : leb_detHom g = 1) : f * g = g * f := by
  have : Fact (Module.finrank ℝ (E 2) = 2) := ⟨by simp⟩
  let o : Orientation ℝ (E 2) (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hpos : ∀ h : (E 2) ≃ₗᵢ[ℝ] (E 2), leb_detHom h = 1 →
      0 < LinearMap.det (h.toLinearEquiv : (E 2) →ₗ[ℝ] (E 2)) := by
    intro h hh
    have : (LinearEquiv.det h.toLinearEquiv : ℝ) = 1 := by
      have := congrArg (fun u : ℝˣ => (u : ℝ)) hh
      exact this
    rw [LinearEquiv.coe_det] at this
    rw [this]; norm_num
  obtain ⟨θ, rfl⟩ := o.exists_linearIsometryEquiv_eq_of_det_pos (hpos f hf)
  obtain ⟨φ, rfl⟩ := o.exists_linearIsometryEquiv_eq_of_det_pos (hpos g hg)
  rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.mul_def, o.rotation_trans,
    o.rotation_trans, add_comm]

theorem leb_linear_isSolvable (hn : n ≤ 2) : Group.IsSolvable ((E n) ≃ₗᵢ[ℝ] (E n)) := by
  rcases Nat.lt_or_eq_of_le hn with h | rfl
  · exact Group.isSolvable_of_comm (leb_linear_comm_of_le_one (by omega))
  · have : Group.IsSolvable (leb_detHom (n := 2)).ker :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (leb_rot_comm a b a.2 b.2)
    exact Group.isSolvable_of_ker_le_range (leb_detHom (n := 2)).ker.subtype leb_detHom
      (by simp)

theorem leb_isometry_isSolvable (hn : n ≤ 2) : Group.IsSolvable ((E n) ≃ᵢ (E n)) := by
  have := leb_linear_isSolvable hn
  exact Group.isSolvable_of_ker_le_range leb_transHom leb_linHom leb_ker_le_range

end Isometry

end Garrido.Lib

namespace Garrido.Lib

open Garrido MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise

section Corollary25

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

theorem leb_measurePreserving (f : (E n) ≃ᵢ (E n)) : MeasurePreserving f volume volume := by
  have hf : (f : (E n) → (E n)) = (fun x => x + f 0) ∘ (leb_lin f) :=
    funext fun v => leb_apply_eq f v
  rw [hf]
  exact (measurePreserving_add_right volume (f 0)).comp (leb_lin f).measurePreserving

theorem leb_image_eq (f : (E n) ≃ᵢ (E n)) (s : Set (E n)) : f '' s = f.symm ⁻¹' s :=
  f.toEquiv.image_eq_preimage_symm s

theorem leb_volume_image (f : (E n) ≃ᵢ (E n)) (s : Set (E n)) : volume (f '' s) = volume s := by
  rw [leb_image_eq]
  exact (leb_measurePreserving f.symm).measure_preimage_emb
    f.symm.toHomeomorph.measurableEmbedding s

theorem leb_nullMeasurable_image (f : (E n) ≃ᵢ (E n)) {s : Set (E n)}
    (hs : NullMeasurableSet s volume) : NullMeasurableSet (f '' s) volume := by
  rw [leb_image_eq]
  exact hs.preimage (leb_measurePreserving f.symm).quasiMeasurePreserving

/-- Isometries act on the space by application. -/
@[reducible] noncomputable def leb_mulAction : MulAction ((E n) ≃ᵢ (E n)) (E n) where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] leb_mulAction

theorem leb_smul_eq_image (f : (E n) ≃ᵢ (E n)) (s : Set (E n)) : f • s = f '' s := by
  rw [← Set.image_smul]; rfl

/-- Corollary 2.5, from Corollary 2.4 and Theorem 2.6 (taken as hypotheses in exactly the
form of those milestones' statements, universe-specialised to `Type`). -/
theorem leb_exists_isometryInvariant_finitelyAdditive_extension_volume
    (h24 : ∀ {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex],
      Group.IsSolvable H → IsAmenable G)
    (h26 : ∀ {G : Type} [Group G], IsAmenable G → HasInvariantExtensionProperty.{0, 0} G)
    (n : ℕ) (hn : n ≤ 2) :
    ∃ m : Set (EuclideanSpace ℝ (Fin n)) → ℝ≥0∞,
      IsFinitelyAdditiveMeasure m ∧
      (∀ (f : EuclideanSpace ℝ (Fin n) ≃ᵢ EuclideanSpace ℝ (Fin n))
        (s : Set (EuclideanSpace ℝ (Fin n))), m (f '' s) = m s) ∧
      (∀ s : Set (EuclideanSpace ℝ (Fin n)),
        MeasureTheory.NullMeasurableSet s MeasureTheory.volume →
          m s = MeasureTheory.volume s) := by
  have hsolv := leb_isometry_isSolvable hn
  have hA : IsAmenable ((E n) ≃ᵢ (E n)) := h24 (⊤ : Subgroup ((E n) ≃ᵢ (E n))) inferInstance
  obtain ⟨ν, hν, hνext⟩ :=
    leb_exists_finitelyAdditive_extension (volume : Measure (E n))
  obtain ⟨m, hm, hmR, hminv⟩ := h26 hA (E n) {s | NullMeasurableSet s volume} volume ν
    (fun f s hs => by rw [leb_smul_eq_image]; exact leb_nullMeasurable_image f hs)
    (fun f s _ => by rw [leb_smul_eq_image]; exact leb_volume_image f s)
    (fun s hs => hνext s hs) hν
  refine ⟨m, hm, fun f s => ?_, fun s hs => hmR s hs⟩
  have := hminv f s
  rwa [leb_smul_eq_image] at this

end Corollary25

end Garrido.Lib

/-!
# Tarski's theorem (Garrido, Theorem 1.11) and Theorem 3.10(2)

Route (see `NOTES-TAR.md`): infinite Hall ⇒ "doubling ⇒ paradox"; iteration ⇒ Følner sets
inside `E` for a non-paradoxical `E`; ultrafilter limit of normalised counting measures on those
sets ⇒ a finitely additive `ν` with `ν E = 1` that is invariant for partial translations inside
`E`; a supremum over finite families of translated pieces extends `ν` to a `G`-invariant
finitely additive measure `m` with `m E = 1`.
-/

namespace Garrido.Lib

open scoped ENNReal Pointwise Classical
open Garrido Set

section Tarski

variable {G X : Type*} [Group G] [MulAction G X]

/-! ### Step 1: doubling inside `E` gives a paradoxical decomposition -/

/-! ### Step 2: expansion by a factor `(k+2)/(k+1)` gives doubling -/

/-! ### Step 3: a non-paradoxical set has Følner sets inside it -/

/-! ### Step 4: normalised counting measures on Følner sets -/

/-! ### Step 5: the limit measure -/

/-! ### Step 6: extension to a `G`-invariant measure on all of `X` -/

/-! ### The easy direction -/

end Tarski

-- Theorem 1.11 (p. 3), Tarski.

end Garrido.Lib

/-!
# Composition of the clusters

Each target below is stated exactly as published and assembled from results proved in the
cluster modules (`AB_`, `CLO_`, `MEAN_`, `EXT_`, `FOL_`, `NAM_`, `EQ_`, `LEB_`, `TAR_`).
-/

namespace Garrido.Lib

open Garrido


/-- Corollary 2.4: `CLO` reduced it to Propositions 2.3 (`AB`) and 2.2(2) (`MEAN`). -/
alias isAmenable_of_isSolvable_of_finiteIndex' := Garrido.isAmenable_of_isSolvable_of_finiteIndex

/-- Theorem 2.6: `EXT`'s construction from an invariant mean, which `MEAN` supplies. -/
alias hasInvariantExtensionProperty_of_isAmenable' := Garrido.hasInvariantExtensionProperty_of_isAmenable

open scoped ENNReal in
/-- Corollary 2.5: `LEB` reduced it to Corollary 2.4 and Theorem 2.6, both composed above. -/
theorem exists_isometryInvariant_finitelyAdditive_extension_volume' (n : ℕ) (hn : n ≤ 2) :
    ∃ m : Set (EuclideanSpace ℝ (Fin n)) → ℝ≥0∞,
      IsFinitelyAdditiveMeasure m ∧
      (∀ (f : EuclideanSpace ℝ (Fin n) ≃ᵢ EuclideanSpace ℝ (Fin n))
        (s : Set (EuclideanSpace ℝ (Fin n))), m (f '' s) = m s) ∧
      (∀ s : Set (EuclideanSpace ℝ (Fin n)),
        MeasureTheory.NullMeasurableSet s MeasureTheory.volume →
          m s = MeasureTheory.volume s) :=
  leb_exists_isometryInvariant_finitelyAdditive_extension_volume
    (fun H _ hH => isAmenable_of_isSolvable_of_finiteIndex' H hH)
    (fun hG => hasInvariantExtensionProperty_of_isAmenable' hG) n hn

end Garrido.Lib

open Garrido
open scoped ENNReal Pointwise

theorem solution (n : ℕ) (hn : n ≤ 2) :
    ∃ m : Set (EuclideanSpace ℝ (Fin n)) → ℝ≥0∞,
      IsFinitelyAdditiveMeasure m ∧
      (∀ (f : EuclideanSpace ℝ (Fin n) ≃ᵢ EuclideanSpace ℝ (Fin n))
        (s : Set (EuclideanSpace ℝ (Fin n))), m (f '' s) = m s) ∧
      (∀ s : Set (EuclideanSpace ℝ (Fin n)),
        MeasureTheory.NullMeasurableSet s MeasureTheory.volume →
          m s = MeasureTheory.volume s) := by
  apply Garrido.Lib.exists_isometryInvariant_finitelyAdditive_extension_volume' <;> assumption
