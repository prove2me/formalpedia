-- Prove2me | solution 1 for DetDLP.column_elimination_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:41:01.369486+00:00
-- url     : https://prove2.me/submissions/f352616b-e883-4516-9039-db12f2a99704

import Definitions.Def_DetDLP_BorderedHermite

namespace DetDLP.BorderedHermite

/-- The underlying two-column Euclidean operation has determinant one. -/
theorem pivot_unimodular (p t : ℤ) (hp : 0 < p) :
    let g : ℤ := p.gcd t
    p.gcdA t * (p/g) + p.gcdB t * (t/g) = 1 := by
  intro g
  have hp' : g*(p/g) = p := Int.mul_ediv_cancel' (Int.gcd_dvd_left ..)
  have ht' : g*(t/g) = t := Int.mul_ediv_cancel' (Int.gcd_dvd_right ..)
  have hne : g ≠ 0 := by intro h; rw [h,zero_mul] at hp'; omega
  apply mul_left_cancel₀ hne
  calc
    _ = p.gcdA t*(g*(p/g))+p.gcdB t*(g*(t/g)) := by ring
    _ = _ := by rw [hp',ht',mul_one]; simpa [g,mul_comm] using (Int.gcd_eq_gcd_ab p t).symm

theorem pivot_row {n : ℕ} (m : ℤ) (j : Fin n) (v w : Column n) (hp : 0 < (v.get j)) :
    (pivotPair m j v w).1.get j = ((v.get j).gcd (w.get j) : ℤ) ∧ (pivotPair m j v w).2.get j = 0 := by
  let p := (v.get j)
  let t := (w.get j)
  let g : ℤ := p.gcd t
  by_cases hz : (w.get j) = 0
  · simp [pivotPair,hz,abs_of_pos hp]
  · simp only [pivotPair,if_neg hz]
    simp only [get_ofFn,trim,lt_irrefl,if_false]
    constructor
    · change p.gcdA t * p + p.gcdB t * t = _
      linear_combination (Int.gcd_eq_gcd_ab p t).symm
    · change -(t/g)*p+(p/g)*t = 0
      have hp' : g*(p/g) = p := Int.mul_ediv_cancel' (Int.gcd_dvd_left ..)
      have ht' : g*(t/g) = t := Int.mul_ediv_cancel' (Int.gcd_dvd_right ..)
      linear_combination -(t/g)*hp'.symm + (p/g)*ht'.symm

abbrev Subgroup (n : ℕ) := AddSubgroup (Fin n → ℤ)

private def grid {n : ℕ} (m : ℤ) (j : Fin n) : Fin n → ℤ := Pi.single j m

private def reserves {n : ℕ} (m : ℤ) (k : ℕ) (H : Subgroup n) : Prop :=
  ∀ i : Fin n, k ≤ i.val → grid m i ∈ H

private def held {n : ℕ} (H : Subgroup n) (xs : Array (Column n)) :=
  ∀ c ∈ xs, c.get ∈ H

private theorem held_push {n : ℕ} (H : Subgroup n) (xs : Array (Column n)) (v) :
    held H (xs.push v) ↔ held H xs ∧ v.get ∈ H := by
  simp [held,Array.mem_push,or_imp,forall_and]

private theorem reserves_succ {n : ℕ} (m : ℤ) (j : Fin n) (H : Subgroup n) :
    reserves m j.val H ↔ grid m j ∈ H ∧ reserves m (j.val+1) H := by
  constructor
  · intro h; exact ⟨h _ le_rfl,fun i hi => h i (by omega)⟩
  · rintro ⟨hj,hs⟩ i hi
    by_cases he : i.val = j.val
    · simpa [Fin.ext he] using hj
    · exact hs i (by omega)

private theorem sub_iff {n : ℕ} (H : Subgroup n) {u v : Fin n → ℤ} (hv : v ∈ H) :
    u-v ∈ H ↔ u ∈ H :=
  ⟨fun h => by simpa using H.add_mem h hv,fun h => H.sub_mem h hv⟩

/-- A reduction by reserved pure columns preserves membership in every subgroup
containing those columns. This handles intermediate tail normalization as well. -/
private theorem reduce_mem_iff {n : ℕ} (m : ℤ) (k : ℕ) (H : Subgroup n)
    (h : reserves m k H) (v : Fin n → ℤ) :
    (fun i : Fin n => if k ≤ i.val then v i % m else v i) ∈ H ↔ v ∈ H := by
  classical
  let q (j : Fin n) := if k ≤ j.val then v j / m else 0
  have hs : ∑ j : Fin n, q j • grid m j ∈ H := by
    apply H.sum_mem
    intro j _
    by_cases hj : k ≤ j.val
    · exact H.zsmul_mem (h j hj) _
    · simp [q,hj]
  have he : (fun i : Fin n => if k ≤ i.val then v i % m else v i) =
      v - ∑ j : Fin n, q j • grid m j := by
    ext i
    simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [grid,q,Pi.single_apply,Int.emod_def,mul_comm]
      split_ifs <;> simp_all
    · intro b _ hb
      simp [grid,Pi.single_apply,hb,Ne.symm hb]
    · simp
  rw [he]
  exact sub_iff H hs

private theorem trim_mem {n : ℕ} (m : ℤ) (j : Fin n) (H : Subgroup n)
    (h : reserves m (j.val+1) H) (v : Fin n → ℤ) :
    (fun i => trim m j i (v i)) ∈ H ↔ v ∈ H := by
  simpa only [trim,Fin.lt_def,Nat.succ_le_iff] using reduce_mem_iff m (j.val+1) H h v

private theorem pair_mem {n : ℕ} (m : ℤ) (j : Fin n) (H : Subgroup n)
    (h : reserves m (j.val+1) H) (v w : Column n) (hp : 0 < v.get j) :
    (pivotPair m j v w).1.get ∈ H ∧ (pivotPair m j v w).2.get ∈ H ↔
      v.get ∈ H ∧ w.get ∈ H := by
  classical
  let p := v.get j
  let t := w.get j
  let g : ℤ := p.gcd t
  let a := p.gcdA t
  let b := p.gcdB t
  let C := a • v.get + b • w.get
  let D := -(t/g) • v.get + (p/g) • w.get
  by_cases hz : w.get j = 0
  · simp [pivotPair,hz]
  · have hv : (pivotPair m j v w).1.get = fun i => trim m j i (C i) := by
      funext i; simp [pivotPair,hz,C,a,b,p,t]
    have hw : (pivotPair m j v w).2.get = fun i => trim m j i (D i) := by
      funext i; simp [pivotPair,hz,D,g,p,t]
    rw [hv,hw,trim_mem m j H h C,trim_mem m j H h D]
    have det : a*(p/g)+b*(t/g)=1 := pivot_unimodular p t hp
    constructor
    · rintro ⟨hC,hD⟩
      have ev : (p/g) • C - b • D = v.get := by
        ext i; simp [C,D]; linear_combination v.get i * det
      have ew : (t/g) • C + a • D = w.get := by
        ext i; simp [C,D]; linear_combination w.get i * det
      exact ⟨ev ▸ H.sub_mem (H.zsmul_mem hC (p/g)) (H.zsmul_mem hD b),
        ew ▸ H.add_mem (H.zsmul_mem hC (t/g)) (H.zsmul_mem hD a)⟩
    · rintro ⟨hV,hW⟩
      exact ⟨H.add_mem (H.zsmul_mem hV a) (H.zsmul_mem hW b),
        H.add_mem (H.zsmul_mem hV (-(t/g))) (H.zsmul_mem hW (p/g))⟩

private def oldZero {n : ℕ} (k : ℕ) (v : Column n) : Prop :=
  ∀ i : Fin n, i.val < k → v.get i = 0

private theorem pair_past {n : ℕ} (m : ℤ) (j : Fin n) (v w : Column n)
    (hv : oldZero j.val v) (hw : oldZero j.val w) :
    oldZero j.val (pivotPair m j v w).1 ∧ oldZero j.val (pivotPair m j v w).2 := by
  by_cases hz : w.get j = 0
  · simpa [pivotPair,hz] using And.intro hv hw
  · constructor <;> intro i hi <;> simp [pivotPair,hz,trim,hv i hi,hw i hi]

private theorem fold_pairs {n : ℕ} (m : ℤ) (j : Fin n) (ws : List (Column n))
    (st : Column n × Array (Column n)) (hp : 0 < st.1.get j)
    (hz : oldZero j.val st.1) (ht : ∀ v ∈ st.2, oldZero (j.val+1) v)
    (hw : ∀ w ∈ ws, oldZero j.val w) :
    let out := ws.foldl (pairStep m j) st
    0 < out.1.get j ∧ oldZero j.val out.1 ∧
      (∀ v ∈ out.2, oldZero (j.val+1) v) ∧
      ∀ H : Subgroup n, reserves m (j.val+1) H →
        (out.1.get ∈ H ∧ held H out.2 ↔
          st.1.get ∈ H ∧ held H st.2 ∧ ∀ w ∈ ws, w.get ∈ H) := by
  induction ws generalizing st with
  | nil => exact ⟨hp,hz,ht,fun _ _ => by simp⟩
  | cons w ws ih =>
    have pw := pivot_row m j st.1 w hp
    have gp : 0 < (pivotPair m j st.1 w).1.get j := by
      rw [pw.1]; exact_mod_cast Int.gcd_pos_of_ne_zero_left _ hp.ne'
    obtain ⟨zo,zr⟩ := pair_past m j st.1 w hz (hw w (by simp))
    have zz : oldZero (j.val+1) (pivotPair m j st.1 w).2 := by
      intro i hi
      by_cases he : i.val = j.val
      · simpa [Fin.ext he] using pw.2
      · exact zr i (by omega)
    have ha : ∀ v ∈ (pairStep m j st w).2, oldZero (j.val+1) v := by
      intro v hv
      rcases Array.mem_push.mp hv with h|rfl
      · exact ht v h
      · exact zz
    obtain ⟨p,z,t,H⟩ := ih (pairStep m j st w) gp zo ha (fun v h => hw v (by simp [h]))
    refine ⟨p,z,t,fun L hL => ?_⟩
    rw [List.foldl_cons,H L hL]
    change (_ ∈ L ∧ held L (st.2.push _) ∧ _) ↔ _
    rw [held_push]
    simp only [List.mem_cons,forall_eq_or_imp]
    have e := pair_mem m j L hL st.1 w hp
    tauto

/-- Each processed row has one positive pivot and the required reduced entries. -/
private def shape {n : ℕ} (k : ℕ) (cols : Array (Column n)) : Prop :=
  cols.size = k ∧ ∀ i : Fin n, i.val < k →
    ∃ d : ℤ, 0 < d ∧ ∀ j : Fin cols.size,
      (if i.val < j.val then cols[j].get i = 0
       else if i.val = j.val then cols[j].get i = d
       else 0 ≤ cols[j].get i ∧ cols[j].get i < d)

private theorem reduceFixed_pre {n : ℕ} (m : ℤ) (j : Fin n) (p c : Column n)
    (hz : oldZero j.val p) (i : Fin n) (hi : i < j) :
    (reduceFixed m j p c).get i = c.get i := by
  simp [reduceFixed,trim,hz i hi,not_lt.mpr hi.le]

private theorem reduceFixed_self {n : ℕ} (m : ℤ) (j : Fin n) (p c : Column n) :
    (reduceFixed m j p c).get j = c.get j % p.get j := by
  simp [reduceFixed,trim,Int.emod_def,mul_comm]

private theorem push_shape {n : ℕ} (m : ℤ) (j : Fin n) (cols : Array (Column n))
    (hs : shape j.val cols) (p : Column n) (hp : 0 < p.get j) (hz : oldZero j.val p) :
    shape (j.val+1) ((cols.map (reduceFixed m j p)).push p) := by
  obtain ⟨hsize,hrows⟩ := hs
  refine ⟨by simp [hsize],?_⟩
  intro i hi
  have hcase (a : Fin ((cols.map (reduceFixed m j p)).push p).size) :
      a.val < cols.size ∨ a.val = cols.size := by
    have ha := a.isLt
    simp only [Array.size_push,Array.size_map] at ha
    omega
  by_cases h : i.val = j.val
  · have ei : i = j := Fin.ext h
    subst i
    refine ⟨p.get j,hp,fun a => ?_⟩
    rcases hcase a with ha|ha
    · have haj : a.val < j.val := by omega
      simp [Array.getElem_push,Array.getElem_map,ha,hsize,show ¬j.val<a.val by omega,
        show j.val≠a.val by omega,haj,reduceFixed_self,Int.emod_nonneg _ hp.ne',Int.emod_lt_of_pos _ hp]
    · simp [Array.getElem_push,ha,hsize]
  · have hi' : i.val < j.val := by omega
    obtain ⟨d,hd,hrow⟩ := hrows i hi'
    refine ⟨d,hd,fun a => ?_⟩
    rcases hcase a with ha|ha
    · have e := hrow (⟨a.val,ha⟩ : Fin cols.size)
      simpa [Array.getElem_push,Array.getElem_map,ha,reduceFixed_pre m j p _ hz i hi'] using e
    · simp [Array.getElem_push,ha,hsize,hi',hz i hi']

private theorem reduceFixed_mem {n : ℕ} (m : ℤ) (j : Fin n) (H : Subgroup n)
    (hr : reserves m (j.val+1) H) (p c : Column n) (hp : p.get ∈ H) :
    (reduceFixed m j p c).get ∈ H ↔ c.get ∈ H := by
  let q := c.get j / p.get j
  have he : (reduceFixed m j p c).get = fun i => trim m j i ((c.get - q • p.get) i) := by
    ext; simp [reduceFixed,q]
  rw [he,trim_mem m j H hr, sub_iff H (H.zsmul_mem hp q)]

private def represents {n : ℕ} (m : ℤ) (k : ℕ) (st : Array (Column n) × Array (Column n))
    (H : Subgroup n) := held H st.1 ∧ held H st.2 ∧ reserves m k H

private theorem stage_inv {n : ℕ} {m : ℤ} (hm : 0 < m) (j : Fin n)
    (st : Array (Column n) × Array (Column n)) (hs : shape j.val st.1)
    (hw : ∀ w ∈ st.2, oldZero j.val w) :
    let st' := pivotStage m j st
    shape (j.val+1) st'.1 ∧ (∀ w ∈ st'.2, oldZero (j.val+1) w) ∧
      ∀ H : Subgroup n, represents m (j.val+1) st' H ↔ represents m j.val st H := by
  let e : Column n := Vector.ofFn (fun i => if i = j then m else 0)
  have eg : e.get = grid m j := by ext i; simp [e,grid,Pi.single_apply]
  have ez : oldZero j.val e := by intro i hi; simp [e,Fin.ne_of_val_ne (by omega : i.val ≠ j.val)]
  let f := st.2.toList.foldl (pairStep m j) (e,#[])
  obtain ⟨hp,hz,ht,hf⟩ := fold_pairs m j st.2.toList (e,#[])
    (by simpa [e] using hm) ez (by simp) (by simpa using hw)
  change shape _ ((st.1.map (reduceFixed m j f.1)).push f.1) ∧
    (∀ w ∈ f.2, _) ∧ _
  refine ⟨push_shape m j st.1 hs f.1 hp hz,ht,fun H => ?_⟩
  change (held H ((st.1.map (reduceFixed m j f.1)).push f.1) ∧ held H f.2 ∧ _) ↔ _
  rw [held_push]
  change _ ↔ held H st.1 ∧ held H st.2 ∧ reserves m j.val H
  rw [reserves_succ m j H]
  by_cases hr : reserves m (j.val+1) H
  · have he : f.1.get ∈ H ∧ held H f.2 ↔ grid m j ∈ H ∧ held H st.2 := by
      simpa [f,held,eg] using hf H hr
    have hh (hp' : f.1.get ∈ H) :
        held H (st.1.map (reduceFixed m j f.1)) ↔ held H st.1 := by
      simp [held,Array.mem_map,reduceFixed_mem m j H hr f.1 _ hp']
    constructor
    · rintro ⟨⟨hm',hp'⟩,ht',_⟩
      obtain ⟨hg,ht''⟩ := he.mp ⟨hp',ht'⟩
      exact ⟨(hh hp').mp hm',ht'',hg,hr⟩
    · rintro ⟨hm',ht',hg,_⟩
      obtain ⟨hp',ht''⟩ := he.mpr ⟨hg,ht'⟩
      exact ⟨⟨(hh hp').mpr hm',hp'⟩,ht'',hr⟩
  · tauto

private theorem rows_inv {n : ℕ} {m : ℤ} (hm : 0 < m) (cols : Array (Column n))
    (k : ℕ) (hk : k ≤ n) :
    let st := runRows m cols k
    shape k st.1 ∧ (∀ w ∈ st.2, oldZero k w) ∧
      ∀ H : Subgroup n, represents m k st H ↔ held H cols ∧ reserves m 0 H := by
  induction k with
  | zero =>
    refine ⟨⟨rfl,by simp⟩,by simp [oldZero],fun H => ?_⟩
    change held H #[] ∧ held H (cols.map fun c => c.map (· % m)) ∧ reserves m 0 H ↔ _
    have he (c : Column n) (hr : reserves m 0 H) : (c.map (· % m)).get ∈ H ↔ c.get ∈ H := by
      have he' : (c.map (· % m)).get = fun i => c.get i % m := by
        ext i; change (c.map (· % m))[i.val] = (c.get i) % m; rw [Vector.getElem_map]; rfl
      rw [he']; simpa using reduce_mem_iff m 0 H hr c.get
    by_cases h : reserves m 0 H
    · simp [held,Array.mem_map,h,he _ h]
    · tauto
  | succ k ih =>
    have hlt : k < n := by omega
    obtain ⟨hs,hw,hr⟩ := ih (by omega)
    obtain ⟨hs',hw',hr'⟩ := stage_inv hm (⟨k,hlt⟩ : Fin n) _ hs hw
    simp only [runRows, dif_pos hlt]
    exact ⟨hs',hw',fun H => (hr' H).trans (hr H)⟩

end DetDLP.BorderedHermite

open DetDLP DetDLP.BorderedHermite
theorem solution {n : ℕ} {m : ℤ} (hm : 0 < m) (cols : Array (Column n)) :
    let out := normalForm m cols
    out.size = n ∧ IsColumnHNF (asMatrix out) ∧
      ∀ H : AddSubgroup (Fin n → ℤ), (∀ c ∈ out, c.get ∈ H) ↔
        (∀ c ∈ cols, c.get ∈ H) ∧ (∀ i : Fin n, (Pi.single i m : Fin n → ℤ) ∈ H) := by
  intro out
  obtain ⟨⟨hs,hrows⟩,hzero,hspan⟩ := rows_inv hm cols n le_rfl
  change out.size = n at hs
  have entry (i j : Fin n) : asMatrix out i j = (out[j.val]'(by rw [hs]; exact j.isLt)).get i := by
    simp [asMatrix,show j.val < out.size by rw [hs]; exact j.isLt]
  have row (i : Fin n) : ∃ d : ℤ, 0 < d ∧ ∀ j : Fin n,
      (if i < j then asMatrix out i j = 0 else if i = j then asMatrix out i j = d
       else 0 ≤ asMatrix out i j ∧ asMatrix out i j < d) := by
    obtain ⟨d,hd,hr⟩ := hrows i i.isLt
    refine ⟨d,hd,fun j => ?_⟩
    rw [entry]
    simpa only [Fin.lt_def,Fin.ext_iff,Fin.getElem_fin,out,normalForm] using hr ⟨j.val,by change j.val < out.size; rw [hs]; exact j.isLt⟩
  refine ⟨hs,⟨?_,?_,?_⟩,?_⟩
  · intro i j hij
    obtain ⟨d,_,hr⟩ := row i
    simpa [hij] using hr j
  · intro i
    obtain ⟨d,hd,hr⟩ := row i
    simpa [show asMatrix out i i = d by simpa using hr i] using hd
  · intro i j hji
    obtain ⟨d,_,hr⟩ := row i
    rw [show asMatrix out i i = d by simpa using hr i]
    simpa [not_lt.mpr hji.le,ne_of_gt hji] using hr j
  · intro H
    have hz : held H (runRows m cols n).2 := by
      intro w hw
      have he : w.get = 0 := funext fun i => hzero w hw i i.isLt
      rw [he]; exact H.zero_mem
    have hr : reserves m n H := fun i h => False.elim (Nat.not_le_of_lt i.isLt h)
    have eq := hspan H
    simp only [represents,hz,hr,and_true] at eq
    simpa only [reserves,Nat.zero_le,forall_true_left,grid,held,out,normalForm] using eq

