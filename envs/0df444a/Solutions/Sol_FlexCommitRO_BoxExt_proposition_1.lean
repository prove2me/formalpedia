-- Prove2me | solution 1 for FlexCommitRO.BoxExt.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T08:40:20.609209+00:00
-- url     : https://prove2.me/submissions/6553c6d1-69a4-465b-8133-49ecc7a90df7

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_Setting
open FlexCommitRO.BoxExt
open scoped BigOperators Classical

namespace FlexCommitProof

variable {T : ℕ}

def corner (lo hi : Fin T → ℝ) (b : Fin T → Bool) (i : Fin T) : ℝ :=
  if b i then hi i else lo i

noncomputable def weight (lo hi d : Fin T → ℝ) (b : Fin T → Bool) : ℝ :=
  ∏ i, if b i then (d i-lo i)/(hi i-lo i) else 1-(d i-lo i)/(hi i-lo i)

noncomputable def interp (lo hi : Fin T → ℝ) (f : (Fin T → ℝ) → ℝ)
    (d : Fin T → ℝ) : ℝ :=
  ∑ b, weight lo hi d b * f (corner lo hi b)

end FlexCommitProof

open scoped BigOperators Classical
open FlexCommitRO.BoxExt

namespace FlexCommitProof

noncomputable section

private def bitWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

private def cubeWeight {ι : Type*} [Fintype ι] (p : ι → ℝ) (b : ι → Bool) : ℝ :=
  ∏ i, bitWeight (p i) (b i)

private theorem cubeWeight_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) :
    ∑ b, cubeWeight p b = 1 := by
  classical
  unfold cubeWeight
  rw [← Fintype.prod_sum]
  simp [bitWeight]

variable {T : ℕ}

 theorem corner_mem (lo hi : Fin T → ℝ) (b : Fin T → Bool) :
    corner lo hi b ∈ Set.univ.pi (fun t => ({lo t, hi t} : Set ℝ)) := by
  intro i _
  simp only [corner]
  split <;> simp

 theorem corner_mem_box {lo hi : Fin T → ℝ} (hlt : ∀ t, lo t < hi t)
    (b : Fin T → Bool) :
    corner lo hi b ∈ Set.univ.pi (fun t => Set.Icc (lo t) (hi t)) := by
  intro i _
  simp only [corner, Set.mem_Icc]
  split <;> exact ⟨by linarith [hlt i], by linarith [hlt i]⟩

 theorem weight_sum (lo hi d : Fin T → ℝ) : ∑ b, weight lo hi d b = 1 := by
  exact cubeWeight_sum (fun i => (d i - lo i) / (hi i - lo i))

 theorem weight_nonneg {lo hi d : Fin T → ℝ} (hlt : ∀ t, lo t < hi t)
    (hd : d ∈ Set.univ.pi (fun t => Set.Icc (lo t) (hi t))) (b : Fin T → Bool) :
    0 ≤ weight lo hi d b := by
  apply Finset.prod_nonneg
  intro i _
  have hdi := hd i (Set.mem_univ i)
  have hp : 0 < hi i - lo i := sub_pos.mpr (hlt i)
  have h0 : 0 ≤ (d i - lo i) / (hi i - lo i) := div_nonneg (sub_nonneg.mpr hdi.1) hp.le
  have h1 : (d i - lo i) / (hi i - lo i) ≤ 1 := (div_le_one hp).mpr (by linarith [hdi.2])
  split <;> linarith

private theorem cubeWeight_split {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (J : ι → Prop) [DecidablePred J] (a : {i // J i} → Bool)
    (c : {i // ¬J i} → Bool) :
    cubeWeight p ((Equiv.piEquivPiSubtypeProd J (fun _ => Bool)).symm (a,c)) =
      cubeWeight (fun i : {i // J i} => p i) a *
      cubeWeight (fun i : {i // ¬J i} => p i) c := by
  classical
  unfold cubeWeight
  have h : (fun i => bitWeight (p i)
      ((Equiv.piEquivPiSubtypeProd J (fun _ => Bool)).symm (a,c) i)) =
      fun i => if h : J i then bitWeight (p i) (a ⟨i,h⟩)
        else bitWeight (p i) (c ⟨i,h⟩) := by
    funext i
    by_cases h : J i <;> simp [Equiv.piEquivPiSubtypeProd, h]
  rw [h, Fintype.prod_dite]

private theorem cubeMean_marginal {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (f : (ι → Bool) → ℝ) (J : ι → Prop) [DecidablePred J]
    (hdep : ∀ b b', (∀ i, J i → b i = b' i) → f b = f b') :
    ∑ b, cubeWeight p b * f b =
      ∑ a : {i // J i} → Bool, cubeWeight (fun i : {i // J i} => p i) a *
        f ((Equiv.piEquivPiSubtypeProd J (fun _ => Bool)).symm (a, fun _ => false)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd J (fun _ => Bool)
  rw [← e.symm.sum_comp (fun b => cubeWeight p b * f b), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have hf (c : {i // ¬J i} → Bool) : f (e.symm (a,c)) = f (e.symm (a,fun _ => false)) := by
    apply hdep
    intro i hi
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  simp_rw [hf]
  dsimp only [e]
  simp_rw [cubeWeight_split]
  rw [← Finset.sum_mul, ← Finset.mul_sum, cubeWeight_sum]
  ring

 theorem weight_prefix {lo hi d d' : Fin T → ℝ} (f : (Fin T → Bool) → ℝ)
    (k : ℕ) (hdep : ∀ b b', (∀ i : Fin T, i.val < k → b i = b' i) → f b = f b')
    (hdd : ∀ i : Fin T, i.val < k → d i = d' i) :
    (∑ b, weight lo hi d b * f b) = ∑ b, weight lo hi d' b * f b := by
  classical
  change (∑ b, cubeWeight (fun i => (d i-lo i)/(hi i-lo i)) b * f b) =
    ∑ b, cubeWeight (fun i => (d' i-lo i)/(hi i-lo i)) b * f b
  rw [cubeMean_marginal _ f (fun i : Fin T => i.val < k) hdep,
    cubeMean_marginal _ f (fun i : Fin T => i.val < k) hdep]
  congr 1
  funext a
  congr 1
  unfold cubeWeight
  apply Finset.prod_congr rfl
  intro i _
  dsimp only
  rw [hdd i i.property]

 theorem weight_coordinate {lo hi : Fin T → ℝ} (hlt : ∀ t, lo t < hi t)
    (d : Fin T → ℝ) (i : Fin T) :
    (∑ b, weight lo hi d b * corner lo hi b i) = d i := by
  classical
  let p : Fin T → ℝ := fun j => (d j - lo j) / (hi j - lo j)
  let e := Equiv.piSplitAt i (fun _ : Fin T => Bool)
  change (∑ b, cubeWeight p b * (if b i then hi i else lo i)) = d i
  rw [← e.symm.sum_comp (fun b => cubeWeight p b * (if b i then hi i else lo i)),
    Fintype.sum_prod_type]
  have hw (b : Bool) (c : {j : Fin T // j ≠ i} → Bool) :
      cubeWeight p (e.symm (b,c)) = bitWeight (p i) b * cubeWeight (fun j => p j.val) c := by
    unfold cubeWeight
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    congr 1
    · simp [e, Equiv.piSplitAt]
    · apply Finset.prod_congr rfl
      intro j _
      simp [e, Equiv.piSplitAt, j.property]
  simp_rw [hw]
  have he (b : Bool) (c : {j : Fin T // j ≠ i} → Bool) : e.symm (b,c) i = b := by
    simp [e, Equiv.piSplitAt]
  simp_rw [he]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, cubeWeight_sum, mul_one]
  simp only [Fintype.sum_bool, bitWeight, Bool.false_eq_true, ↓reduceIte]
  dsimp [p]
  field_simp [ne_of_gt (sub_pos.mpr (hlt i))]
  ring

end
end FlexCommitProof

open scoped BigOperators Classical

namespace FlexCommitProof
noncomputable section
variable {T : ℕ}

 theorem interp_const (lo hi d : Fin T → ℝ) (r : ℝ) :
    interp lo hi (fun _ => r) d = r := by
  unfold interp
  rw [← Finset.sum_mul, weight_sum, one_mul]

 theorem interp_add (lo hi : Fin T → ℝ) (f g : (Fin T → ℝ) → ℝ) (d : Fin T → ℝ) :
    interp lo hi (fun v => f v + g v) d = interp lo hi f d + interp lo hi g d := by
  simp only [interp, mul_add, Finset.sum_add_distrib]

 theorem interp_sub (lo hi : Fin T → ℝ) (f g : (Fin T → ℝ) → ℝ) (d : Fin T → ℝ) :
    interp lo hi (fun v => f v - g v) d = interp lo hi f d - interp lo hi g d := by
  simp only [interp, mul_sub, Finset.sum_sub_distrib]

 theorem interp_mul (lo hi : Fin T → ℝ) (r : ℝ) (f : (Fin T → ℝ) → ℝ) (d : Fin T → ℝ) :
    interp lo hi (fun v => r * f v) d = r * interp lo hi f d := by
  simp only [interp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

 theorem interp_sum {I : Type*} (s : Finset I) (f : I → (Fin T → ℝ) → ℝ)
    (lo hi d : Fin T → ℝ) :
    interp lo hi (fun v => ∑ i ∈ s, f i v) d = ∑ i ∈ s, interp lo hi (f i) d := by
  unfold interp
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

 theorem interp_coordinate {lo hi : Fin T → ℝ} (hlt : ∀ t, lo t < hi t)
    (d : Fin T → ℝ) (i : Fin T) : interp lo hi (fun v => v i) d = d i :=
  weight_coordinate hlt d i

 theorem interp_mono {lo hi d : Fin T → ℝ} (hlt : ∀ t, lo t < hi t)
    (hd : d ∈ Set.univ.pi (fun t => Set.Icc (lo t) (hi t)))
    {f g : (Fin T → ℝ) → ℝ}
    (hf : ∀ b, f (corner lo hi b) ≤ g (corner lo hi b)) :
    interp lo hi f d ≤ interp lo hi g d := by
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (hf b) (weight_nonneg hlt hd b)

 theorem interp_prefix (lo hi : Fin T → ℝ) (f : (Fin T → ℝ) → ℝ) (k : ℕ)
    (hdep : ∀ b b',
      (∀ i : Fin T, i.val < k → corner lo hi b i = corner lo hi b' i) →
      f (corner lo hi b) = f (corner lo hi b'))
    (d d' : Fin T → ℝ) (hdd : ∀ i : Fin T, i.val < k → d i = d' i) :
    interp lo hi f d = interp lo hi f d' := by
  apply weight_prefix (fun b => f (corner lo hi b)) k ?_ hdd
  intro b b' hb
  apply hdep b b'
  intro i hi
  simp only [corner, hb i hi]

end
end FlexCommitProof

open scoped BigOperators Classical

namespace FlexCommitProof
noncomputable section
variable {T : ℕ}

 theorem interp_ereal_upper {lo hi d : Fin T → ℝ} (hlt : ∀ t, lo t < hi t)
    (hd : d ∈ Set.univ.pi (fun t => Set.Icc (lo t) (hi t)))
    (f : (Fin T → ℝ) → ℝ) (U : EReal)
    (hf : ∀ b, (f (corner lo hi b) : EReal) ≤ U) :
    (interp lo hi f d : EReal) ≤ U := by
  induction U using EReal.rec with
  | bot => simpa using hf (fun _ => false)
  | coe r =>
      have h : interp lo hi f d ≤ interp lo hi (fun _ => r) d :=
        interp_mono hlt hd (fun b => EReal.coe_le_coe_iff.mp (hf b))
      rw [interp_const] at h
      exact EReal.coe_le_coe_iff.mpr h
  | top => exact le_top

 theorem interp_ereal_lower {lo hi d : Fin T → ℝ} (hlt : ∀ t, lo t < hi t)
    (hd : d ∈ Set.univ.pi (fun t => Set.Icc (lo t) (hi t)))
    (f : (Fin T → ℝ) → ℝ) (L : EReal)
    (hf : ∀ b, L ≤ (f (corner lo hi b) : EReal)) :
    L ≤ (interp lo hi f d : EReal) := by
  induction L using EReal.rec with
  | bot => exact bot_le
  | coe r =>
      have h : interp lo hi (fun _ => r) d ≤ interp lo hi f d :=
        interp_mono hlt hd (fun b => EReal.coe_le_coe_iff.mp (hf b))
      rw [interp_const] at h
      exact EReal.coe_le_coe_iff.mpr h
  | top => simpa using hf (fun _ => false)

 theorem interp_le_corner_sup {lo hi d : Fin T → ℝ} (hlt : ∀ t, lo t < hi t)
    (hd : d ∈ Set.univ.pi (fun t => Set.Icc (lo t) (hi t)))
    (f : (Fin T → ℝ) → ℝ) :
    (interp lo hi f d : EReal) ≤
      ⨆ v ∈ Set.univ.pi (fun t => ({lo t, hi t} : Set ℝ)), (f v : EReal) := by
  apply interp_ereal_upper hlt hd f
  intro b
  exact le_iSup_of_le (corner lo hi b) (le_iSup_of_le (corner_mem lo hi b) le_rfl)

end
end FlexCommitProof

open FlexCommitRO.BoxExt
open scoped BigOperators Classical

namespace FlexCommitProof

variable {T : ℕ}

noncomputable def extendPolicy (lo hi : Fin T → ℝ) (pol : RSFCPolicy T) : RSFCPolicy T where
  w := pol.w
  z := pol.z
  q := fun t => interp lo hi (pol.q t)
  y := fun t => interp lo hi (pol.y t)
  u := fun t => interp lo hi (pol.u t)
  x := fun k => interp lo hi (pol.x k)

lemma interp_congr (lo hi : Fin T → ℝ) (f g : (Fin T → ℝ) → ℝ)
    (h : ∀ b, f (corner lo hi b) = g (corner lo hi b)) (d : Fin T → ℝ) :
    interp lo hi f d = interp lo hi g d := by
  unfold interp
  apply Finset.sum_congr rfl
  intro b _
  rw [h b]

lemma corners_subset_box {lo hi : Fin T → ℝ} (hlt : ∀ t, lo t < hi t) :
    Set.univ.pi (fun t => ({lo t, hi t} : Set ℝ)) ⊆
      Set.univ.pi (fun t => Set.Icc (lo t) (hi t)) := by
  intro d hd i _
  have h := hd i (Set.mem_univ i)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> simp [h, le_of_lt (hlt i)]

lemma extension_nonanticipative (lo hi : Fin T → ℝ) (pol : RSFCPolicy T)
    (hna : NonAnticipative (fun t => ({lo t, hi t} : Set ℝ)) pol) :
    NonAnticipative (fun t => Set.Icc (lo t) (hi t)) (extendPolicy lo hi pol) := by
  intro d _ d' _
  constructor
  · intro t hdd
    have dep (b b' : Fin T → Bool)
        (h : ∀ i : Fin T, i.val < t.val → corner lo hi b i = corner lo hi b' i) :=
      (hna _ (corner_mem lo hi b) _ (corner_mem lo hi b')).1 t
        (fun i hi => h i hi)
    have he : ∀ i : Fin T, i.val < t.val → d i = d' i := fun i hi => hdd i hi
    exact ⟨interp_prefix lo hi (pol.q t) t.val (fun b b' h => (dep b b' h).1) d d' he,
      interp_prefix lo hi (pol.y t) t.val (fun b b' h => (dep b b' h).2.1) d d' he,
      interp_prefix lo hi (pol.u t) t.val (fun b b' h => (dep b b' h).2.2) d d' he⟩
  · intro k hdd
    exact interp_prefix lo hi (pol.x k) k.val
      (fun b b' h => (hna _ (corner_mem lo hi b) _ (corner_mem lo hi b')).2 k h)
      d d' hdd

lemma extension_feasible (D : RSFCData T) (lo hi : Fin T → ℝ)
    (hlt : ∀ t, lo t < hi t) (pol : RSFCPolicy T)
    (hp : Feasible D (fun t => ({lo t, hi t} : Set ℝ)) pol) :
    Feasible D (fun t => Set.Icc (lo t) (hi t)) (extendPolicy lo hi pol) := by
  refine ⟨extension_nonanticipative lo hi pol hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_⟩
  intro d hd
  have hf (b : Fin T → Bool) := hp.2.2.2.2 _ (corner_mem lo hi b)
  constructor
  · change interp lo hi (pol.x 0) d = D.x₁
    calc
      _ = interp lo hi (fun _ => D.x₁) d := interp_congr lo hi _ _ (fun b => (hf b).1) d
      _ = _ := interp_const lo hi d D.x₁
  · intro t
    have hb : interp lo hi (pol.x t.succ) d =
        interp lo hi (pol.x t.castSucc) d + interp lo hi (pol.q t) d - d t := by
      calc
        _ = interp lo hi (fun v => pol.x t.castSucc v + pol.q t v - v t) d :=
          interp_congr lo hi _ _ (fun b => ((hf b).2 t).1) d
        _ = _ := by rw [interp_sub, interp_add, interp_coordinate hlt]
    have hlo := interp_ereal_lower hlt hd (pol.q t) (D.L t)
      (fun b => ((hf b).2 t).2.1)
    have hhi := interp_ereal_upper hlt hd (pol.q t) (D.U t)
      (fun b => ((hf b).2 t).2.2.1)
    have hclo := interp_ereal_lower hlt hd
      (fun v => ∑ τ ∈ Finset.univ.filter (· ≤ t), pol.q τ v) (D.Lhat t)
      (fun b => ((hf b).2 t).2.2.2.1)
    have hchi := interp_ereal_upper hlt hd
      (fun v => ∑ τ ∈ Finset.univ.filter (· ≤ t), pol.q τ v) (D.Uhat t)
      (fun b => ((hf b).2 t).2.2.2.2.1)
    rw [interp_sum] at hclo hchi
    have hy1 := interp_mono (f := fun v => hbar D t * pol.x t.succ v) (g := pol.y t) hlt hd
      (fun b => ((hf b).2 t).2.2.2.2.2.1)
    have hy2 := interp_mono (f := fun v => -D.p t * pol.x t.succ v) (g := pol.y t) hlt hd
      (fun b => ((hf b).2 t).2.2.2.2.2.2.1)
    have hu1 := interp_mono (f := fun v => D.αp t * (pol.q t v - pol.w t)) (g := pol.u t) hlt hd
      (fun b => ((hf b).2 t).2.2.2.2.2.2.2.1)
    have hu2 := interp_mono (f := fun v => -D.αm t * (pol.q t v - pol.w t)) (g := pol.u t) hlt hd
      (fun b => ((hf b).2 t).2.2.2.2.2.2.2.2)
    simp only [interp_mul, interp_sub, interp_const] at hy1 hy2 hu1 hu2
    exact ⟨hb, hlo, hhi, hclo, hchi, hy1, hy2, hu1, hu2⟩

lemma extension_cost (D : RSFCData T) (lo hi : Fin T → ℝ) (pol : RSFCPolicy T)
    (d : Fin T → ℝ) :
    cost D (extendPolicy lo hi pol) d = interp lo hi (cost D pol) d := by
  unfold cost
  rw [interp_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [interp_add, interp_mul, interp_const, extendPolicy]

lemma restriction_feasible (D : RSFCData T) (lo hi : Fin T → ℝ)
    (hlt : ∀ t, lo t < hi t) (pol : RSFCPolicy T)
    (hp : Feasible D (fun t => Set.Icc (lo t) (hi t)) pol) :
    Feasible D (fun t => ({lo t, hi t} : Set ℝ)) pol := by
  refine ⟨?_, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_⟩
  · intro d hd d' hd'
    exact hp.1 d (corners_subset_box hlt hd) d' (corners_subset_box hlt hd')
  · intro d hd
    exact hp.2.2.2.2 d (corners_subset_box hlt hd)

end FlexCommitProof

namespace FlexCommitRO.BoxExt

theorem proposition_1 {T : ℕ} (D : RSFCData T) (dmin dmax : Fin T → ℝ)
    (hlt : ∀ t, dmin t < dmax t) :
    value D (fun t => Set.Icc (dmin t) (dmax t)) =
      value D (fun t => ({dmin t, dmax t} : Set ℝ)) := by
  apply le_antisymm
  · unfold value
    apply le_iInf
    intro pol
    apply le_iInf
    intro hp
    apply iInf_le_of_le (FlexCommitProof.extendPolicy dmin dmax pol)
    apply iInf_le_of_le (FlexCommitProof.extension_feasible D dmin dmax hlt pol hp)
    apply iSup_le
    intro d
    apply iSup_le
    intro hd
    rw [FlexCommitProof.extension_cost]
    exact FlexCommitProof.interp_le_corner_sup hlt hd (cost D pol)
  · unfold value
    apply le_iInf
    intro pol
    apply le_iInf
    intro hp
    apply iInf_le_of_le pol
    apply iInf_le_of_le (FlexCommitProof.restriction_feasible D dmin dmax hlt pol hp)
    apply iSup_le
    intro d
    apply iSup_le
    intro hd
    exact le_iSup_of_le d (le_iSup_of_le (FlexCommitProof.corners_subset_box hlt hd) le_rfl)

end FlexCommitRO.BoxExt

open FlexCommitRO.BoxExt

theorem solution {T : ℕ} (D : RSFCData T) (dmin dmax : Fin T → ℝ)
    (hlt : ∀ t, dmin t < dmax t) :
    value D (fun t => Set.Icc (dmin t) (dmax t)) =
      value D (fun t => ({dmin t, dmax t} : Set ℝ)) := by
  exact FlexCommitRO.BoxExt.proposition_1 D dmin dmax hlt
